#!/bin/bash
export TERM=xterm
#echo "admin.sh:/dev/tcp/$1/$2"
REPLY="y"
set -e
until test $REPLY = "n"
do
   (hostname;top -b  -n 1|grep instantiate) >/dev/tcp/$1/$2
done
