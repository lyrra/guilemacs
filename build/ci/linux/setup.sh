#!/usr/bin/env bash

echo "Setup Linux build environment"

df -h .

apt_packages_basic=(
  file
  git
  pkg-config
  software-properties-common
  unzip
  p7zip-full
  )

# These are the same as on Travis CI
apt_packages_standard=(
  curl
  libfontconfig1-dev
  libfreetype6-dev
  libfreetype6
  libgl1-mesa-dev
  libnss3-dev
  libzmq3-dev
  libgnutls28-dev
  libgif-dev
  make
  gcc
  wget
  xaw3dg-dev
  )
# Cant use distributions guile, since it isn't adapted for elisp
#  guile-3.0
#  guile-3.0-dev
#  guile-3.0-libs
#  guile-bytestructures
#  guile-json
#  guile-sqlite3

apt_packages_runtime=(
  # Alphabetical order please!
  libcups2
  libdbus-1-3
  libegl1-mesa-dev
  libodbc1
  libpq-dev
  libssl-dev
  libxcomposite-dev
  libxcursor-dev
  libxi-dev
  libxkbcommon-x11-0
  libxrandr2
  libxtst-dev
  libdrm-dev
  )

sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  "${apt_packages_basic[@]}" \
  "${apt_packages_standard[@]}" \
  "${apt_packages_runtime[@]}"

# install guile-elisp

# FIX: get latest release using API: https://docs.github.com/en/rest/releases/releases?apiVersion=2022-11-28#list-releases

wget https://github.com/lyrra/guile/releases/download/release-elisp-20240101-1658/linux-x86_64-guile3-elisp.tar.xz

tar xvf linux-x86_64-guile3-elisp.tar.xz

ls -ltr

export PATH=`pwd`/libguile/.libs:$PATH

echo "---------- whereis guile 3.0 ------------"
command -v guile || true
echo "-------- %library-dir / SCM_LIBRARY_DIR ------------------------------"
guile -c '(begin (display (%library-dir)) (newline))'
echo "------------------------------------------------------"

apt-get clean autoclean
apt-get autoremove --purge -y

df -h .
echo "Setup script done"

