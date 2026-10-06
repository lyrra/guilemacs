/* Lisp functions for making directory listings.
   Copyright (C) 1985-1986, 1993-1994, 1999-2025 Free Software
   Foundation, Inc.

This file is part of GNU Emacs.

GNU Emacs is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or (at
your option) any later version.

GNU Emacs is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.  */


#include <config.h>

#include <sys/stat.h>

#ifdef HAVE_PWD_H
#include <pwd.h>
#endif
#include <grp.h>

#include <errno.h>
#include <fcntl.h>
#include <unistd.h>

#include <dirent.h>
#include <filemode.h>
#include <stat-time.h>

#include "lisp.h"
#include "systime.h"
#include "buffer.h"
#include "coding.h"

/* FIX-20261005-guilemacs: M49 imp-2 -- the typed C leaves below use the
   Guile string API over plain values.  */
#include "guile.h"

#ifdef MSDOS
#include "msdos.h"	/* for fstatat */
#endif

#if !(defined HAVE_ANDROID && !defined ANDROID_STUBIFY)
typedef DIR emacs_dir;
#define emacs_readdir readdir
#define emacs_closedir closedir
#else

#include "android.h"

/* The Android emulation of dirent stuff is required to be able to
   list the /assets special directory.  */
typedef struct android_vdir emacs_dir;
#define emacs_readdir android_readdir
#define emacs_closedir android_closedir
#endif

#ifdef WINDOWSNT
extern int is_slow_fs (const char *);
#endif

static ptrdiff_t scmp (const char *, const char *, ptrdiff_t);
static Lisp_Object file_attributes (int, char const *, Lisp_Object,
				    Lisp_Object, Lisp_Object);

/* Return the number of bytes in DP's name.  */
static ptrdiff_t
dirent_namelen (struct dirent *dp)
{
#ifdef _D_EXACT_NAMLEN
  return _D_EXACT_NAMLEN (dp);
#else
  return strlen (dp->d_name);
#endif
}

#ifndef HAVE_STRUCT_DIRENT_D_TYPE
#if !defined (DT_UNKNOWN) && !defined (DT_DIR) && !defined (DT_LNK)
enum {
  DT_UNKNOWN,
  DT_DIR,
  DT_LNK,
};
#elif defined (DT_UNKNOWN) && defined (DT_DIR) && defined (DT_LNK)
/* Nothing to do here, all three are defined as macros.  */
#elif defined (DT_UNKNOWN) || defined (DT_DIR) || defined (DT_LNK)
#error "Cannot determine DT_UNKNOWN, DT_DIR, DT_LNK"
#endif
#endif

/* Return the file type of DP.  */
static int
dirent_type (struct dirent *dp)
{
#ifdef HAVE_STRUCT_DIRENT_D_TYPE
  return dp->d_type;
#else
  return DT_UNKNOWN;
#endif
}

static emacs_dir *
open_directory (Lisp_Object dirname, Lisp_Object encoded_dirname, int *fdp)
{
  char *name = SSDATA (encoded_dirname);
  emacs_dir *d;
  int fd, opendir_errno;

  fd = emacs_open (name, O_RDONLY | O_DIRECTORY, 0);
  if (fd < 0)
    {
      opendir_errno = errno;
      d = 0;
    }
  else
    {
      d = fdopendir (fd);
      opendir_errno = errno;
      if (! d)
	emacs_close (fd);
    }

  if (!d)
    {
      xsignal2 (Qerror, build_string ("opening directory"), Qnil);
      report_file_errno ("Opening directory", dirname, opendir_errno);
    }
  *fdp = fd;
  return d;
}

static void
directory_files_internal_unwind (void *d)
{
  emacs_closedir (d);
}

/* Return the next directory entry from DIR; DIR's name is DIRNAME.
   If there are no more directory entries, return a null pointer.
   Signal any unrecoverable errors.  */

static struct dirent *
read_dirent (emacs_dir *dir, Lisp_Object dirname)
{
  while (true)
    {
      errno = 0;
      struct dirent *dp = emacs_readdir (dir);
      if (dp || errno == 0)
	return dp;
      if (! (errno == EAGAIN || errno == EINTR))
	{
	  report_file_error ("Reading directory", dirname);
	}
      maybe_quit ();
    }
}

/* FIX-20261006-guilemacs: M49 imp-3.  Return the RAW name list of
   DIRECTORY as a plain list of strings, in readdir order.  It holds the
   mechanism only: Fdirectory_file_name, ENCODE_FILE, open_directory, the
   dynwind guard, the readdir loop, and maybe_quit.  It runs no match, no
   separator, no full join, no count, and no sort.  The Scheme policy
   (emacs dired) dired-listing-names computes that decision.  It must not
   call Fdirectory_files or directory_files_internal, or a hub rewire
   would recurse (docs/kb.org leaf-must-call-the-mechanism).  */

static Lisp_Object
dired_read_names_1 (Lisp_Object directory)
{
  Lisp_Object dirfilename = Fdirectory_file_name (directory);
  Lisp_Object encoded_dirfilename = ENCODE_FILE (dirfilename);

  int fd;
  emacs_dir *d = open_directory (dirfilename, encoded_dirfilename, &fd);
  (void) fd;

  dynwind_begin ();
  record_unwind_protect_ptr (directory_files_internal_unwind, d);

  Lisp_Object names = Qnil;
  for (struct dirent *dp; (dp = read_dirent (d, directory)); )
    {
      ptrdiff_t len = dirent_namelen (dp);
      names = Fcons (scm_from_utf8_stringn (dp->d_name, len), names);
      maybe_quit ();
    }

  dynwind_end ();

  return Fnreverse (names);
}

/* Function shared by Fdirectory_files and Fdirectory_files_and_attributes.
   If not ATTRS, return a list of directory filenames;
   if ATTRS, return a list of directory filenames and their attributes.
   In the latter case, pass ID_FORMAT to file_attributes.  */

Lisp_Object
directory_files_internal (Lisp_Object directory, Lisp_Object full,
			  Lisp_Object match, Lisp_Object nosort, bool attrs,
			  Lisp_Object id_format, Lisp_Object return_count)
{
  EMACS_INT ind = 0, last = MOST_POSITIVE_FIXNUM;

  if (!NILP (return_count))
    {
      CHECK_FIXNAT (return_count);
      last = XFIXNAT (return_count);
    }

  if (!NILP (match))
    CHECK_STRING (match);

  /* Don't let the compiler optimize away all copies of DIRECTORY,
     which would break GC; see Bug#16986.  */
  Lisp_Object volatile directory_volatile = directory;

  Lisp_Object dirfilename = Fdirectory_file_name (directory);

  /* Note: ENCODE_FILE and DECODE_FILE can GC because they can run
     run_pre_post_conversion_on_str which calls Lisp directly and
     indirectly.  */
  Lisp_Object encoded_dirfilename = ENCODE_FILE (dirfilename);

  int fd;

  /* Keep in mind that FD is not always a real file descriptor on
     Android.  */
  emacs_dir *d = open_directory (dirfilename, encoded_dirfilename, &fd);

  /* Unfortunately, we can now invoke expand-file-name and
     file-attributes on filenames, both of which can throw, so we must
     do a proper unwind-protect.  */
  dynwind_begin ();
  record_unwind_protect_ptr (directory_files_internal_unwind, d);

#ifdef WINDOWSNT
  Lisp_Object w32_save = Qnil;
  if (attrs)
    {
      /* Do this only once to avoid doing it (in w32.c:stat) for each
	 file in the directory, when we call file_attributes below.  */
      record_unwind_protect (directory_files_internal_w32_unwind,
			     Vw32_get_true_file_attributes);
      if (EQ (Vw32_get_true_file_attributes, Qlocal))
	{
	  /* w32.c:stat will notice these bindings and avoid calling
	     GetDriveType for each file.  */
	  if (is_slow_fs (SSDATA (encoded_dirfilename)))
	    Vw32_get_true_file_attributes = Qnil;
	  else
	    Vw32_get_true_file_attributes = Qt;
	}
    }
#endif

#if 0
  if (!NILP (full))
    { /* We will be concatenating 'directory' with local file name.
         We always decode local file names, so in order to safely concatenate
         them we need 'directory' to be decoded as well (bug#56469).  */
      directory = DECODE_FILE (directory);
    }
#endif

  ptrdiff_t directory_nbytes = SBYTES (directory);
  re_match_object = Qt;

  /* Decide whether we need to add a directory separator.  */
  bool needsep = (directory_nbytes == 0
		  || !IS_ANY_SEP (SREF (directory, directory_nbytes - 1)));

  /* Windows users want case-insensitive wildcards.  */
  Lisp_Object case_table = Qnil;
#ifdef WINDOWSNT
  case_table = BVAR (&buffer_defaults, case_canon_table);
#endif

  /* Read directory entries and accumulate them into LIST.  */
  Lisp_Object list = Qnil;
  for (struct dirent *dp; (dp = read_dirent (d, directory)); )
    {
      ptrdiff_t len = dirent_namelen (dp);
      Lisp_Object name = scm_from_utf8_stringn (dp->d_name, len);
      Lisp_Object finalname = name;

      maybe_quit ();

      if (!NILP (match)
	  && fast_string_match_internal (match, name, case_table) < 0)
	continue;

      Lisp_Object fileattrs UNINIT;
      if (attrs)
	{
	  fileattrs = file_attributes (fd, dp->d_name, directory, name,
				       id_format);
	  if (NILP (fileattrs))
	    continue;
	}

      if (!NILP (full))
	{
	  ptrdiff_t name_nbytes = SBYTES (name);
	  ptrdiff_t nbytes = directory_nbytes + needsep + name_nbytes;
	  ptrdiff_t nchars = SCHARS (directory) + needsep + SCHARS (name);
	  /* DECODE_FILE may return non-ASCII unibyte strings (e.g. when
             file-name-coding-system is 'binary'), so we don't know for sure
             that the bytes we have follow our internal utf-8 representation
             for multibyte strings.  If nchars == nbytes we don't need to
             care and just return a unibyte string; and if not, that means
             one of 'name' or 'directory' is multibyte, in which case we
             presume that the other one would also be multibyte if it
             contained non-ASCII.
             FIXME: This last presumption is broken when 'directory' is
             multibyte (with non-ASCII), and 'name' is unibyte with non-ASCII
             (because file-name-coding-system is 'binary').  */
	  finalname = make_uninit_string (nchars);

          int dirlen = scm_c_string_length (directory);
          for (int i = 0; i < dirlen; i++)
            {
              scm_c_string_set_x (finalname, i,
                                  scm_c_string_ref (directory, i));
            }

	  if (needsep)
	    // SSET (finalname, directory_nbytes, DIRECTORY_SEP);
            scm_c_string_set_x (finalname, directory_nbytes, scm_c_make_char (DIRECTORY_SEP));
	  //memcpy (SDATA (finalname) + directory_nbytes + needsep,
		  //SDATA (name), name_nbytes);
          for (int i = 0; i < name_nbytes; i++)
            {
              scm_c_string_set_x (finalname, directory_nbytes + needsep + i,
                                  scm_c_string_ref (name, i));
            }
	}
      else
	finalname = name;

      if (ind == last)
          break;
      ind ++;

      list = Fcons (attrs ? Fcons (finalname, fileattrs) : finalname, list);
    }

  dynwind_end ();

  if (NILP (nosort))
    {
      Lisp_Object ordered = Fnreverse (list);
      list = CALLN (Fsort, ordered,
		    attrs ? Qfile_attributes_lessp : Qstring_lessp);
    }

  (void) directory_volatile;
  return list;
}

/* FIX-20261006-guilemacs: M49 imp-3 -- the G1 dispatch helper over the
   listing policy of (emacs dired).  The C hub reads the raw names with
   dired_read_names_1; the module computes the separator, the full join,
   the match, the count, and the sort key.  It passes plain values only:
   the name list, the directory string, and the four plain arguments of
   `directory-files'.  */

static Lisp_Object
dired_listing_names_scheme (Lisp_Object names, Lisp_Object directory,
			    Lisp_Object full, Lisp_Object match,
			    Lisp_Object nosort, Lisp_Object count)
{
  static SCM proc = SCM_UNDEFINED;
  SCM args[6];
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs dired", "dired-listing-names");
  args[0] = names; args[1] = directory; args[2] = full;
  args[3] = match; args[4] = nosort; args[5] = count;
  return SCM_CALL_N (proc, args, 6);
}


DEFUN ("directory-files", Fdirectory_files, Sdirectory_files, 1, 5, 0,
       doc: /* Return a list of names of files in DIRECTORY.
There are four optional arguments:
If FULL is non-nil, return absolute file names.  Otherwise return names
 that are relative to the specified directory.
If MATCH is non-nil, mention only file names whose non-directory part
 matches the regexp MATCH.
If NOSORT is non-nil, the list is not sorted--its order is unpredictable.
 Otherwise, the list returned is sorted with `string-lessp'.
 NOSORT is useful if you plan to sort the result yourself.
If COUNT is non-nil and a natural number, the function will return
 COUNT number of file names (if so many are present).  */)
  (Lisp_Object directory, Lisp_Object full, Lisp_Object match,
   Lisp_Object nosort, Lisp_Object count)
{
  directory = Fexpand_file_name (directory, Qnil);

  /* If the file name has special constructs in it,
     call the corresponding file name handler.  */
  Lisp_Object handler = Ffind_file_name_handler (directory, Qdirectory_files);
  if (!NILP (handler))
    return call6 (handler, Qdirectory_files, directory,
                  full, match, nosort, count);

  /* FIX-20261006-guilemacs: M49 imp-3.  The G1 listing decision (the
     separator, the full join, the match, the count, and the sort key)
     moved to Scheme.  C reads the raw names and calls the module policy;
     the readdir loop and the unwind guard stay in dired_read_names_1.  */
  Lisp_Object names = dired_read_names_1 (directory);
  return dired_listing_names_scheme (names, directory, full, match, nosort,
                                     count);
}

DEFUN ("directory-files-and-attributes", Fdirectory_files_and_attributes,
       Sdirectory_files_and_attributes, 1, 6, 0,
       doc: /* Return a list of names of files and their attributes in DIRECTORY.
Value is a list of the form:

  ((FILE1 . FILE1-ATTRS) (FILE2 . FILE2-ATTRS) ...)

where each FILEn-ATTRS is the attributes of FILEn as returned
by `file-attributes'.

This function accepts five optional arguments:
If FULL is non-nil, return absolute file names.  Otherwise return names
 that are relative to the specified directory.
If MATCH is non-nil, mention only file names whose non-directory part
 matches the regexp MATCH.
If NOSORT is non-nil, the list is not sorted--its order is unpredictable.
 NOSORT is useful if you plan to sort the result yourself.
ID-FORMAT specifies the preferred format of attributes uid and gid, see
 `file-attributes' for further documentation.
If COUNT is non-nil and a natural number, the function will return
 COUNT number of file names (if so many are present).
On MS-Windows, performance depends on `w32-get-true-file-attributes',
which see.  */)
  (Lisp_Object directory, Lisp_Object full, Lisp_Object match,
   Lisp_Object nosort, Lisp_Object id_format, Lisp_Object count)
{
  directory = Fexpand_file_name (directory, Qnil);

  /* If the file name has special constructs in it,
     call the corresponding file name handler.  */
  Lisp_Object handler
    = Ffind_file_name_handler (directory, Qdirectory_files_and_attributes);
  if (!NILP (handler))
    return call7 (handler, Qdirectory_files_and_attributes,
                  directory, full, match, nosort, id_format, count);

  return directory_files_internal (directory, full, match, nosort,
				   true, id_format, count);
}


static Lisp_Object file_name_completion (Lisp_Object, Lisp_Object, bool,
					 Lisp_Object);

DEFUN ("file-name-completion", Ffile_name_completion, Sfile_name_completion,
       2, 3, 0,
       doc: /* Complete file name FILE in directory DIRECTORY.
Returns the longest string
common to all file names in DIRECTORY that start with FILE.
If there is only one and FILE matches it exactly, returns t.
Returns nil if DIRECTORY contains no name starting with FILE.

If PREDICATE is non-nil, call PREDICATE with each possible
completion (in absolute form) and ignore it if PREDICATE returns nil.

This function ignores some of the possible completions as determined
by the variables `completion-regexp-list' and
`completion-ignored-extensions', which see.  `completion-regexp-list'
is matched against file and directory names relative to DIRECTORY.  */)
  (Lisp_Object file, Lisp_Object directory, Lisp_Object predicate)
{
  Lisp_Object handler;
  directory = Fexpand_file_name (directory, Qnil);

  /* If the directory name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (directory, Qfile_name_completion);
  if (!NILP (handler))
    return call4 (handler, Qfile_name_completion, file, directory, predicate);

  /* If the file name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (file, Qfile_name_completion);
  if (!NILP (handler))
    return call4 (handler, Qfile_name_completion, file, directory, predicate);

  return file_name_completion (file, directory, 0, predicate);
}

DEFUN ("file-name-all-completions", Ffile_name_all_completions,
       Sfile_name_all_completions, 2, 2, 0,
       doc: /* Return a list of all completions of file name FILE in directory DIRECTORY.
These are all file names in directory DIRECTORY which begin with FILE.

This function ignores some of the possible completions as determined
by `completion-regexp-list', which see.  `completion-regexp-list'
is matched against file and directory names relative to DIRECTORY.  */)
  (Lisp_Object file, Lisp_Object directory)
{
  Lisp_Object handler;
  directory = Fexpand_file_name (directory, Qnil);

  /* If the directory name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (directory, Qfile_name_all_completions);
  if (!NILP (handler))
    return call3 (handler, Qfile_name_all_completions, file, directory);

  /* If the file name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (file, Qfile_name_all_completions);
  if (!NILP (handler))
    return call3 (handler, Qfile_name_all_completions, file, directory);

  return file_name_completion (file, directory, 1, Qnil);
}

static bool file_name_completion_dirp (int, struct dirent *, ptrdiff_t);

static Lisp_Object
file_name_completion (Lisp_Object file, Lisp_Object dirname, bool all_flag,
		      Lisp_Object predicate)
{
  ptrdiff_t bestmatchsize = 0;
  int matchcount = 0;
  /* If ALL_FLAG is 1, BESTMATCH is the list of all matches, decoded.
     If ALL_FLAG is 0, BESTMATCH is either nil
     or the best match so far, not decoded.  */
  Lisp_Object bestmatch, tem, elt, name;
  Lisp_Object encoded_file;
  Lisp_Object encoded_dir;
  bool directoryp;
  /* If not INCLUDEALL, exclude files in completion-ignored-extensions as
     well as "." and "..".  Until shown otherwise, assume we can't exclude
     anything.  */
  bool includeall = 1;
  bool check_decoded = false;
  dynwind_begin ();

  elt = Qnil;

  CHECK_STRING (file);

  bestmatch = Qnil;
  encoded_file = encoded_dir = Qnil;
  specbind_guile (Qdefault_directory, dirname);

  /* Do completion on the encoded file name
     because the other names in the directory are (we presume)
     encoded likewise.  We decode the completed string at the end.  */
  /* Actually, this is not quite true any more: we do most of the completion
     work with decoded file names, but we still do some filtering based
     on the encoded file name.  */
  encoded_file = ENCODE_FILE (file);
  encoded_dir = ENCODE_FILE (Fdirectory_file_name (dirname));

  Lisp_Object file_encoding = Vfile_name_coding_system;
  if (NILP (Vfile_name_coding_system))
    file_encoding = Vdefault_file_name_coding_system;
  /* If the file-name encoding decomposes characters, as we do for
     HFS+ filesystems, we need to make an additional comparison of
     decoded names in order to filter false positives, such as "a"
     falsely matching "a-ring".  */
  if (!NILP (file_encoding)
      && !NILP (plist_get (Fcoding_system_plist (file_encoding),
			   Qdecomposed_characters)))
    {
      check_decoded = true;
      if (STRING_MULTIBYTE (file))
	{
	  /* Recompute FILE to make sure any decomposed characters in
	     it are re-composed by the post-read-conversion.
	     Otherwise, any decomposed characters will be rejected by
	     the additional check below.  */
	  file = DECODE_FILE (encoded_file);
	}
    }
  int fd;
  emacs_dir *d = open_directory (dirname, encoded_dir, &fd);
  record_unwind_protect_ptr (directory_files_internal_unwind, d);

  /* Loop reading directory entries.  */
  Lisp_Object zero = make_fixnum (0);
  ptrdiff_t enc_file_len = SCHARS (encoded_file);
  Lisp_Object file_len = make_fixnum (SCHARS (file));
  for (struct dirent *dp; (dp = read_dirent (d, dirname)); )
    {
      ptrdiff_t len = dirent_namelen (dp);
      bool canexclude = 0;

      maybe_quit ();

      if (len < enc_file_len
	  /* scmp cannot reliably compare non-ASCII strings while
	     ignoring letter-case.  */
	  || (!completion_ignore_case
	      && scmp (dp->d_name, SSDATA (encoded_file), enc_file_len) >= 0))
	continue;

      name = make_unibyte_string (dp->d_name, len);
      name = DECODE_FILE (name);
      ptrdiff_t name_blen = SBYTES (name), name_len = SCHARS (name);
      if (completion_ignore_case
	  && !BASE_EQ (Fcompare_strings (name, zero, file_len, file, zero,
					 file_len, Qt),
		       Qt))
	    continue;

      switch (dirent_type (dp))
	{
	case DT_DIR:
	  directoryp = true;
	  break;

	case DT_LNK: case DT_UNKNOWN:
	  directoryp = file_name_completion_dirp (fd, dp, len);
	  break;

	default:
	  directoryp = false;
	  break;
	}

      tem = Qnil;
      /* If all_flag is set, always include all.
	 It would not actually be helpful to the user to ignore any possible
	 completions when making a list of them.  */
      if (!all_flag)
	{
	  ptrdiff_t skip;
	  Lisp_Object cmp_len = make_fixnum (name_len);

#if 0 /* FIXME: The `scmp' call compares an encoded and a decoded string. */
	  /* If this entry matches the current bestmatch, the only
	     thing it can do is increase matchcount, so don't bother
	     investigating it any further.  */
	  if (!completion_ignore_case
	      /* The return result depends on whether it's the sole match.  */
	      && matchcount > 1
	      && !includeall /* This match may allow includeall to 0.  */
	      && len >= bestmatchsize
	      && 0 > scmp (dp->d_name, SSDATA (bestmatch), bestmatchsize))
	    continue;
#endif

	  if (directoryp)
	    {
#ifndef TRIVIAL_DIRECTORY_ENTRY
#define TRIVIAL_DIRECTORY_ENTRY(n) (!strcmp (n, ".") || !strcmp (n, ".."))
#endif
	      /* "." and ".." are never interesting as completions, and are
		 actually in the way in a directory with only one file.  */
	      if (TRIVIAL_DIRECTORY_ENTRY (dp->d_name))
		canexclude = 1;
	      else if (len > enc_file_len)
		/* Ignore directories if they match an element of
		   completion-ignored-extensions which ends in a slash.  */
		for (tem = Vcompletion_ignored_extensions;
		     CONSP (tem); tem = XCDR (tem))
		  {
		    ptrdiff_t elt_len;
		    char *p1;

		    elt = XCAR (tem);
		    if (!STRINGP (elt))
		      continue;
		    elt_len = SBYTES (elt) - 1; /* -1 for trailing / */
		    if (elt_len <= 0)
		      continue;
		    p1 = SSDATA (elt);
		    if (p1[elt_len] != '/')
		      continue;
		    skip = name_blen - elt_len;
		    if (skip < 0)
		      continue;

		    if (!completion_ignore_case
			&& scmp (SSDATA (name) + skip, p1, elt_len) >= 0)
		      continue;
		    if (completion_ignore_case)
		      {
			elt_len = SCHARS (elt) - 1;
			skip = name_len - elt_len;
			cmp_len = make_fixnum (elt_len);
			if (skip < 0
			    || !BASE_EQ (Fcompare_strings (name,
							   make_fixnum (skip),
							   Qnil,
							   elt, zero, cmp_len,
							   Qt),
					 Qt))
			  continue;
		      }
		    break;
		  }
	    }
	  else
	    {
	      /* Compare extensions-to-be-ignored against end of this file name */
	      /* if name is not an exact match against specified string */
	      if (len > enc_file_len)
		/* and exit this for loop if a match is found */
		for (tem = Vcompletion_ignored_extensions;
		     CONSP (tem); tem = XCDR (tem))
		  {
		    elt = XCAR (tem);
		    if (!STRINGP (elt)) continue;
		    ptrdiff_t elt_len = SBYTES (elt);
		    skip = len - elt_len;
		    if (skip < 0) continue;

		    if (!completion_ignore_case
			&& (scmp (SSDATA (name) + skip, SSDATA (elt), elt_len)
			    >= 0))
		      continue;
		    if (completion_ignore_case)
		      {
			elt_len = SCHARS (elt);
			skip = name_len - elt_len;
			cmp_len = make_fixnum (elt_len);
			if (skip < 0
			    || !BASE_EQ (Fcompare_strings (name,
							   make_fixnum (skip),
							   Qnil,
							   elt, zero, cmp_len,
							   Qt),
					 Qt))
			  continue;
		      }
		    break;
		  }
	    }

	  /* If an ignored-extensions match was found,
	     don't process this name as a completion.  */
	  if (CONSP (tem))
	    canexclude = 1;

	  if (!includeall && canexclude)
	    /* We're not including all files and this file can be excluded.  */
	    continue;

	  if (includeall && !canexclude)
	    { /* If we have one non-excludable file, we want to exclude the
		 excludable files.  */
	      includeall = 0;
	      /* Throw away any previous excludable match found.  */
	      bestmatch = Qnil;
	      bestmatchsize = 0;
	      matchcount = 0;
	    }
	}

      Lisp_Object regexps, table = (completion_ignore_case
				    ? Vascii_canon_table : Qnil);

      /* Ignore this element if it fails to match all the regexps.  */
      for (regexps = Vcompletion_regexp_list; CONSP (regexps);
	   regexps = XCDR (regexps))
	if (fast_string_match_internal (XCAR (regexps), name, table) < 0)
	  break;

      if (CONSP (regexps))
	continue;

      /* This is a possible completion */
      if (directoryp)
	/* This completion is a directory; make it end with '/'.  */
	name = Ffile_name_as_directory (name);

      /* Test the predicate, if any.  */
      if (!NILP (predicate) && NILP (call1 (predicate, name)))
	continue;

      /* Reject entries where the encoded strings match, but the
         decoded don't.  For example, "a" should not match "a-ring" on
         file systems that store decomposed characters. */
      if (check_decoded && SCHARS (file) <= SCHARS (name))
	{
	  /* FIXME: This is a copy of the code below.  */
	  ptrdiff_t compare = SCHARS (file);
	  Lisp_Object cmp
	    = Fcompare_strings (name, zero, make_fixnum (compare),
				file, zero, make_fixnum (compare),
				completion_ignore_case ? Qt : Qnil);
	  if (!BASE_EQ (cmp, Qt))
	    continue;
	}

      /* Suitably record this match.  */

      matchcount += matchcount <= 1;

      if (all_flag)
	bestmatch = Fcons (name, bestmatch);
      else if (NILP (bestmatch))
	{
	  bestmatch = name;
	  bestmatchsize = SCHARS (name);
	}
      else
	{
	  /* FIXME: This is a copy of the code in Ftry_completion.  */
	  ptrdiff_t compare = min (bestmatchsize, SCHARS (name));
	  Lisp_Object cmp
	    = Fcompare_strings (bestmatch, zero, make_fixnum (compare),
				name, zero, make_fixnum (compare),
				completion_ignore_case ? Qt : Qnil);
	  ptrdiff_t matchsize = BASE_EQ (cmp, Qt)
	                        ? compare : eabs (XFIXNUM (cmp)) - 1;

	  if (completion_ignore_case)
	    {
	      /* If this is an exact match except for case,
		 use it as the best match rather than one that is not
		 an exact match.  This way, we get the case pattern
		 of the actual match.  */
	      /* This tests that the current file is an exact match
		 but BESTMATCH is not (it is too long).  */
	      if ((matchsize == SCHARS (name)
		   && matchsize + directoryp < SCHARS (bestmatch))
		  ||
		  /* If there is no exact match ignoring case,
		     prefer a match that does not change the case
		     of the input.  */
		  /* If there is more than one exact match aside from
		     case, and one of them is exact including case,
		     prefer that one.  */
		  /* This == checks that, of current file and BESTMATCH,
		     either both or neither are exact.  */
		  (((matchsize == SCHARS (name))
		    ==
		    (matchsize + directoryp == SCHARS (bestmatch)))
		   && (cmp = Fcompare_strings (name, zero,
					       make_fixnum (SCHARS (file)),
					       file, zero,
					       Qnil,
					       Qnil),
		       BASE_EQ (Qt, cmp))
		   && (cmp = Fcompare_strings (bestmatch, zero,
					       make_fixnum (SCHARS (file)),
					       file, zero,
					       Qnil,
					       Qnil),
		       ! BASE_EQ (Qt, cmp))))
		bestmatch = name;
	    }
	  bestmatchsize = matchsize;

	  /* If the best completion so far is reduced to the string
	     we're trying to complete, then we already know there's no
	     other completion, so there's no point looking any further.  */
	  if (matchsize <= SCHARS (file)
	      && !includeall /* A future match may allow includeall to 0.  */
	      /* If completion-ignore-case is non-nil, don't
		 short-circuit because we want to find the best
		 possible match *including* case differences.  */
	      && (!completion_ignore_case || matchsize == 0)
	      /* The return value depends on whether it's the sole match.  */
	      && matchcount > 1)
	    break;

	}
    }

  /* This closes the directory.  */
  dynwind_end ();

  if (all_flag || NILP (bestmatch))
    return bestmatch;
  /* Return t if the supplied string is an exact match (counting case);
     it does not require any change to be made.  */
  if (matchcount == 1 && !NILP (Fequal (bestmatch, file)))
    return Qt;
  bestmatch = Fsubstring (bestmatch, make_fixnum (0),
			  make_fixnum (bestmatchsize));
  return bestmatch;
}

/* Compare exactly LEN chars of strings at S1 and S2,
   ignoring case if appropriate.
   Return -1 if strings match,
   else number of chars that match at the beginning.  */

static ptrdiff_t
scmp (const char *s1, const char *s2, ptrdiff_t len)
{
  register ptrdiff_t l = len;

  if (completion_ignore_case)
    {
      /* WARNING: This only works for pure ASCII strings, as we
	 compare bytes, not characters!  Use Fcompare_strings for
	 comparing non-ASCII strings case-insensitively.  */
      while (l
	     && (downcase ((unsigned char) *s1++)
		 == downcase ((unsigned char) *s2++)))
	l--;
    }
  else
    {
      while (l && *s1++ == *s2++)
	l--;
    }
  if (l == 0)
    return -1;
  else
    return len - l;
}

/* Return true if in the directory FD the directory entry DP, whose
   string length is LEN, is that of a subdirectory that can be searched.  */
static bool
file_name_completion_dirp (int fd, struct dirent *dp, ptrdiff_t len)
{
  USE_SAFE_ALLOCA;
  char *subdir_name = SAFE_ALLOCA (len + 2);
  memcpy (subdir_name, dp->d_name, len);
  strcpy (subdir_name + len, "/");

  bool dirp = sys_faccessat (fd, subdir_name,
			     F_OK, AT_EACCESS) == 0;
  SAFE_FREE ();
  return dirp;
}

static char *
stat_uname (struct stat *st)
{
#ifdef WINDOWSNT
  return st->st_uname;
#else
  struct passwd *pw = getpwuid (st->st_uid);

  if (pw)
    return pw->pw_name;
  else
    return NULL;
#endif
}

static char *
stat_gname (struct stat *st)
{
#ifdef WINDOWSNT
  return st->st_gname;
#else
  struct group *gr = getgrgid (st->st_gid);

  if (gr)
    return gr->gr_name;
  else
    return NULL;
#endif
}

DEFUN ("file-attributes", Ffile_attributes, Sfile_attributes, 1, 2, 0,
       doc: /* Return a list of attributes of file FILENAME.
Value is nil if specified file does not exist.

ID-FORMAT specifies the preferred format of attributes uid and gid (see
below) - valid values are `string' and `integer'.  The latter is the
default, but we plan to change that, so you should specify a non-nil value
for ID-FORMAT if you use the returned uid or gid.

To access the elements returned, the following access functions are
provided: `file-attribute-type', `file-attribute-link-number',
`file-attribute-user-id', `file-attribute-group-id',
`file-attribute-access-time', `file-attribute-modification-time',
`file-attribute-status-change-time', `file-attribute-size',
`file-attribute-modes', `file-attribute-inode-number', and
`file-attribute-device-number'.

Elements of the attribute list are:
 0. t for directory, string (name linked to) for symbolic link, or nil.
 1. Number of links to file.
 2. File uid as a string or (if ID-FORMAT is `integer' or a string value
  cannot be looked up) as an integer.
 3. File gid, likewise.
 4. Last access time, in the style of `current-time'.
  (See a note below about access time on FAT-based filesystems.)
 5. Last modification time, likewise.  This is the time of the last
  change to the file's contents.
 6. Last status change time, likewise.  This is the time of last change
  to the file's attributes: owner and group, access mode bits, etc.
 7. Size in bytes, as an integer.
 8. File modes, as a string of ten letters or dashes as in ls -l.
 9. An unspecified value, present only for backward compatibility.
10. inode number, as a nonnegative integer.
11. Filesystem device identifier, as an integer or a cons cell of integers.

Large integers are bignums, so `eq' might not work on them.
On most filesystems, the combination of the inode and the device
identifier uniquely identifies the file.  This unique file identification
is provided by the access function `file-attribute-file-identifier'.

On MS-Windows, performance depends on `w32-get-true-file-attributes',
which see.

On some FAT-based filesystems, only the date of last access is recorded,
so last access time will always be midnight of that day.  */)
  (Lisp_Object filename, Lisp_Object id_format)
{
  Lisp_Object encoded;
  Lisp_Object handler;

  filename = internal_condition_case_2 (Fexpand_file_name, filename, Qnil,
					Qt, Fidentity);
  if (!STRINGP (filename))
    return Qnil;

  /* If the file name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (filename, Qfile_attributes);
  if (!NILP (handler))
    { /* Only pass the extra arg if it is used to help backward
	 compatibility with old file name handlers which do not
	 implement the new arg.  --Stef */
      if (NILP (id_format))
	return call2 (handler, Qfile_attributes, filename);
      else
	return call3 (handler, Qfile_attributes, filename, id_format);
    }

  encoded = ENCODE_FILE (filename);
  return file_attributes (AT_FDCWD, SSDATA (encoded), Qnil, filename,
			  id_format);
}

static Lisp_Object
file_attributes (int fd, char const *name,
		 Lisp_Object dirname, Lisp_Object filename,
		 Lisp_Object id_format)
{
  struct stat s;

  dynwind_begin ();

  /* An array to hold the mode string generated by filemodestring,
     including its terminating space and null byte.  */
  char modes[sizeof "-rwxr-xr-x "];

  char *uname = NULL, *gname = NULL;

  int err = EINVAL;

#if defined O_PATH && !defined HAVE_CYGWIN_O_PATH_BUG	\
  && !(defined HAVE_ANDROID && !defined ANDROID_STUBIFY)
  int namefd = emacs_openat (fd, name, O_PATH | O_CLOEXEC | O_NOFOLLOW, 0);
  if (namefd < 0)
    err = errno;
  else
    {
      record_unwind_protect_int (close_file_unwind, namefd);
      if (sys_fstat (namefd, &s) != 0)
	{
	  err = errno;
	  /* The Linux kernel before version 3.6 does not support
	     fstat on O_PATH file descriptors.  Handle this error like
	     missing support for O_PATH.  */
	  if (err == EBADF)
	    err = EINVAL;
	}
      else
	{
	  err = 0;
	  fd = namefd;
	  name = "";
	}
    }
#endif

  if (err == EINVAL)
    {
#ifdef WINDOWSNT
      /* We usually don't request accurate owner and group info,
	 because it can be expensive on Windows to get that, and most
	 callers of 'lstat' don't need that.  But here we do want that
	 information to be accurate.  */
      w32_stat_get_owner_group = 1;
#endif
      err = emacs_fstatat (fd, name, &s, AT_SYMLINK_NOFOLLOW) == 0 ? 0 : errno;
#ifdef WINDOWSNT
      w32_stat_get_owner_group = 0;
#endif
    }

  if (err != 0)
    {
      Lisp_Object tem = file_attribute_errno (filename, err);
      dynwind_end ();
      return tem;
    }

  Lisp_Object file_type;
  if (S_ISLNK (s.st_mode))
    {
      /* On systems lacking O_PATH support there is a race if the
	 symlink is replaced between the call to fstatat and the call
	 to emacs_readlinkat.  Detect this race unless the replacement
	 is also a symlink.  */
      file_type = check_emacs_readlinkat (fd, filename, name);
      if (NILP (file_type))
        {
          dynwind_end ();
	  return Qnil;
        }
    }
  else
    file_type = S_ISDIR (s.st_mode) ? Qt : Qnil;

  dynwind_end ();

  if (!(NILP (id_format) || EQ (id_format, Qinteger)))
    {
      uname = stat_uname (&s);
      gname = stat_gname (&s);
    }

  filemodestring (&s, modes);

  return CALLN (Flist,
		file_type,
		make_fixnum (s.st_nlink),
		(uname
		 ? DECODE_SYSTEM (build_unibyte_string (uname))
		 : INT_TO_INTEGER (s.st_uid)),
		(gname
		 ? DECODE_SYSTEM (build_unibyte_string (gname))
		 : INT_TO_INTEGER (s.st_gid)),
		make_lisp_time (get_stat_atime (&s)),
		make_lisp_time (get_stat_mtime (&s)),
		make_lisp_time (get_stat_ctime (&s)),

		/* If the file size is a 4-byte type, assume that
		   files of sizes in the 2-4 GiB range wrap around to
		   negative values, as this is a common bug on older
		   32-bit platforms.  */
		INT_TO_INTEGER (sizeof (s.st_size) == 4
			    ? s.st_size & 0xffffffffu
			    : s.st_size),

		make_string (modes, 10),
		Qt,
		INT_TO_INTEGER (s.st_ino),
		INT_TO_INTEGER (s.st_dev));
}

/* FIX-20261006-guilemacs: M49 imp-4 -- the G3 dispatch helper over the
   attribute predicate of (emacs dired).  The C hub `file-attributes-lessp'
   extracts Fcar of each attribute list (an attribute list must not cross
   the layer; docs/kb.org leaf-may-narrow-the-argument-shape) and passes
   the two plain names.  The module computes the compare with
   %string-lessp.  The delta is one dispatch-helper public-ref lookup.  */

static Lisp_Object
dired_file_attributes_lessp_scheme (Lisp_Object name1, Lisp_Object name2)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs dired", "dired-file-attributes-lessp");
  return SCM_CALL_2 (proc, name1, name2);
}

DEFUN ("file-attributes-lessp", Ffile_attributes_lessp,
       Sfile_attributes_lessp, 2, 2, 0,
       doc: /* Return t if first arg file attributes list is less than second.
Comparison is in lexicographic order and case is significant.  */)
  (Lisp_Object f1, Lisp_Object f2)
{
  /* FIX-20261006-guilemacs: M49 imp-4.  The attribute predicate decision
     (%string-lessp) moved to Scheme (emacs dired).  C keeps the Fcar
     extraction and calls the module policy.  */
  return dired_file_attributes_lessp_scheme (Fcar (f1), Fcar (f2));
}


DEFUN ("system-users", Fsystem_users, Ssystem_users, 0, 0, 0,
       doc: /* Return a list of user names currently registered in the system.
If we don't know how to determine that on this platform, just
return a list with one element, taken from `user-real-login-name'.  */)
     (void)
{
  Lisp_Object users = Qnil;
#if defined HAVE_GETPWENT && defined HAVE_ENDPWENT
  struct passwd *pw;

  while ((pw = getpwent ()))
    users = Fcons (DECODE_SYSTEM (build_string (pw->pw_name)), users);

  endpwent ();
#endif
  if (NILP (users))
    /* At least current user is always known. */
    users = list1 (Vuser_real_login_name);
  return users;
}

DEFUN ("system-groups", Fsystem_groups, Ssystem_groups, 0, 0, 0,
       doc: /* Return a list of user group names currently registered in the system.
The value may be nil if not supported on this platform.  */)
     (void)
{
  Lisp_Object groups = Qnil;
#if defined HAVE_GETGRENT && defined HAVE_ENDGRENT
  struct group *gr;

  while ((gr = getgrent ()))
    groups = Fcons (DECODE_SYSTEM (build_string (gr->gr_name)), groups);

  endgrent ();
#endif
  return groups;
}

/* FIX-20261005-guilemacs: M49 imp-2.  The typed C --dired-* leaves over
   plain values for the src/dired.c directory / attribute boundary.  Each
   leaf returns one plain value (a string, a boolean, or a list of plain
   strings) and holds the decision of its MOVES block; the caller passes
   plain values in.  The mechanism (the readdir loop, fdopendir,
   emacs_fstatat, sys_faccessat, getpwent / getgrent, filemodestring,
   scmp, and every file-name-handler call) stays in C.  imp-2 adds leaves
   only: it moves no policy.  imp-3 (G1 and G2) and imp-4 (G3) rewire the
   C hubs onto these leaves and delete the inline policy.  See
   docs/m49-plan.org section 3.3 and brief.org section 4.

   M49 imp-3 DELETED the G1 leaf (the listing-names pass-through): the
   listing decision moved into (emacs dired) dired-listing-names.  The
   hub Fdirectory_files now calls the static dired_read_names_1 (the raw
   readdir mechanism) and the G1 Scheme policy (brief.org section 7.3).

   M49 imp-4 DELETED the G3 attribute-predicate leaf: the attribute
   predicate moved into (emacs dired) dired-file-attributes-lessp.  So 2
   leaves remain, both G2
   (--dired-file-name-completion, --dired-file-name-all-completions).
   G2 returns A2 (brief.org section 7.5): the prefix match stays in the
   C loop, because a Scheme match on decoded names cannot replace the
   encoded scmp match at an acceptable delta (brief.org section 6).  So
   the 2 G2 leaves and the 2 G2 hubs are unchanged.

   A leaf returns plain values only: no struct dirent *, struct stat *,
   DIR *, char *, struct passwd *, struct group *, Lisp_Object, or
   attribute list crosses the layer (the M42 rule).  A leaf calls the
   MECHANISM, never its own hub, so a later hub rewire cannot recurse.  */

/* --- G2: the completion policy ------------------------------------- */

DEFUN ("--dired-file-name-completion", Fdired_file_name_completion,
       Sdired_file_name_completion, 3, 3, 0,
       doc: /* FIX-20261005-guilemacs: Internal: complete FILE in
directory DIRECTORY and return one *plain string*, t for a sole exact
match, or nil.  DIRECTORY, FILE, and PREDICATE are plain arguments.  The
mechanism (the readdir loop, the scmp compare, and the DECODE_FILE call)
stays in C (the M42 rule).  M49 imp-2, docs/m49-plan.org section
3.3.  */)
  (Lisp_Object directory, Lisp_Object file, Lisp_Object predicate)
{
  Lisp_Object handler;
  directory = Fexpand_file_name (directory, Qnil);

  /* If the directory name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (directory, Qfile_name_completion);
  if (!NILP (handler))
    return call4 (handler, Qfile_name_completion, file, directory, predicate);

  /* If the file name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (file, Qfile_name_completion);
  if (!NILP (handler))
    return call4 (handler, Qfile_name_completion, file, directory, predicate);

  return file_name_completion (file, directory, 0, predicate);
}

DEFUN ("--dired-file-name-all-completions",
       Fdired_file_name_all_completions, Sdired_file_name_all_completions,
       2, 2, 0,
       doc: /* FIX-20261005-guilemacs: Internal: return all completions of
FILE in directory DIRECTORY as a *plain list* of strings.  The list is
sorted so the result is deterministic.  DIRECTORY and FILE are plain
strings.  The mechanism (the readdir loop, the scmp compare, and the
DECODE_FILE call) stays in C (the M42 rule).  M49 imp-2,
docs/m49-plan.org section 3.3.  */)
  (Lisp_Object directory, Lisp_Object file)
{
  Lisp_Object handler;
  directory = Fexpand_file_name (directory, Qnil);

  /* If the directory name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (directory, Qfile_name_all_completions);
  if (!NILP (handler))
    return call3 (handler, Qfile_name_all_completions, file, directory);

  /* If the file name has special constructs in it,
     call the corresponding file name handler.  */
  handler = Ffind_file_name_handler (file, Qfile_name_all_completions);
  if (!NILP (handler))
    return call3 (handler, Qfile_name_all_completions, file, directory);

  Lisp_Object completions = file_name_completion (file, directory, 1, Qnil);
  /* The raw all-flag path returns the entries in readdir order, so the
     result is not deterministic.  Return a sorted (deterministic) plain
     name list.  */
  return CONSP (completions)
	   ? CALLN (Fsort, completions, Qstring_lessp)
	   : completions;
}

void
syms_of_dired (void)
{
#include "dired.x"

  DEFSYM (Qdirectory_files, "directory-files");
  DEFSYM (Qdirectory_files_and_attributes, "directory-files-and-attributes");
  DEFSYM (Qfile_name_completion, "file-name-completion");
  DEFSYM (Qfile_name_all_completions, "file-name-all-completions");
  DEFSYM (Qfile_attributes, "file-attributes");
  DEFSYM (Qfile_attributes_lessp, "file-attributes-lessp");
  DEFSYM (Qdefault_directory, "default-directory");
  DEFSYM (Qdecomposed_characters, "decomposed-characters");

  DEFVAR_LISP ("completion-ignored-extensions", Vcompletion_ignored_extensions,
	       doc: /* Completion ignores file names ending in any string in this list.
It does not ignore them if all possible completions end in one of
these strings or when displaying a list of completions.
It ignores directory names if they match any string in this list which
ends in a slash.  */);
  Vcompletion_ignored_extensions = Qnil;
}
