#!/bin/bash
current_file_dir=$(dirname "$0")
export PYTHONPATH_DIR="$current_file_dir/../src"

PYTHONPATH=$PYTHONPATH_DIR python /Users/ruihe/mnt/lpp/lpp/utils/visualizer/interactive.py