#!/bin/sh
sed -e "s/<infomsg>//g" $1  | sed -e "s/<\/infomsg>//g" > $2
