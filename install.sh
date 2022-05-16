#!/bin/bash

DIR="$( cd "$( dirname "$0" )" && pwd )"
REL_DIR="/src/FloTest"
FULLDIR="${DIR}${REL_DIR}"

echo "full directory: ${FULLDIR}"

FILE="/resources_directory.txt"
FULLFILE="${FULLDIR}${FILE}"

echo "path file: ${FULLFILE}"

echo ${FULLDIR} > ${FULLFILE}

sudo apt-get update  # To get the latest package lists
sudo apt-get install libjson-c-dev -y

sudo apt-get install python3-dev
sudo apt install python3-pip
sudo apt-get install graphviz graphviz-dev

pip install --upgrade pip
pip install -r requirements.txt
pip install . --verbose
