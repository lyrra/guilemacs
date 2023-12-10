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
  guile-3.0
  guile-3.0-dev
  guile-3.0-libs
  guile-bytestructures
  guile-json
  guile-sqlite3
  make
  gcc
  wget
  )

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

echo "---------- whereis guile 3.0 ------------"
ls -ltr /usr/bin/guile || true
ls -ltr /usr/bin/guile-3.0 || true
command -v guile || true
echo "------------ dir /usr/lib/x86_64-linux-gnu/guile  ---------------------"
find /usr/lib/x86_64-linux-gnu/guile || true
echo "-------- %library-dir / SCM_LIBRARY_DIR ------------------------------"
guile -c '(begin (display (%library-dir)) (newline))'
echo "------------------------------------------------------"
echo "-------- GUILE_SYSTEM_COMPILED_PATH=$GUILE_SYSTEM_COMPILED_PATH ------------------------------"

apt-get clean autoclean
apt-get autoremove --purge -y
rm -rf /tmp/* /var/{cache,log,backups}/* /var/lib/apt/*

df -h .
echo "Setup script done"

