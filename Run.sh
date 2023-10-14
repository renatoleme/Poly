#!/bin/bash

logic=$1
implementation=$2

coqc -Q . Main Poly.v

# if implementation is not given, use 1 as implementation
if [ -z "$implementation" ]
then
    implementation=1
fi

cd $logic

# if logic=IPL , then coqc iLF.v first

if [ $logic = "IPL" ]
then
    coqc iLF.v
fi

coqc $logic$implementation.v