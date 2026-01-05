#!/bin/bash

set -e -x

yosys synth.ys
yosys synth_sky130.ys

