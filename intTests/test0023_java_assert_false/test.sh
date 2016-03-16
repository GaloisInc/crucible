#!/bin/sh

if ! $SAW side.saw ; then
    exit 0
else
    exit 1
fi
