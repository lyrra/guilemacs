In essence this is a rebase attempt of Robin Templeton's 2015 work
on replacing the emacs interpreter/compiler written in C+elisp
with an guile based version.

Some additional work is also done. More info on this is needed.

Branch information
==================

* main

  Use this branch if you want to try it out!
  This branch has the latest effort of Guile-Emacs.

  This branch is just a pointer to the most recent rebase branch.

  Currently this branch tracks branch e28.2

* branch e28.2

  Rebasing the attempt from 2019. Trying to squash many additional (cleanup) commits.

  Based on emacs version 28.2

* guile-20230101

  Rebasing the attempt from 2019. Trying to squash many additional (cleanup) commits.

  Based on emacs version 27.0.50.

* guile-20190824

  2019's rebase attempt. Succeded to the point of running alot of
  elisp code. New patches has been added to fix bugs and bitrot.

  Based on emacs version 26.2.90.

* 2015-guile-wip

  Original work from 2015 by Robin Templeton.

  Based on emacs version 24.4.50.

  - Added later patches from Robin.
  - Added patches to work against the rebased work of guile-elisp to guile3

* master

  Tracks vanilla-emacs
