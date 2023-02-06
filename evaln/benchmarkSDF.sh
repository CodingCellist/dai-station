#! /usr/bin/env bash

#
# Script for evaluating the Dai constraint solver.
# Copyright (c) 2023, Thomas E. Hansen (CodingCellist)
# SPDX-License-Identifier: BSD-3-Clause
#

cd ../src

# quickly build the thing
echo ":q" | idris2 --no-banner --no-colour -p contrib Dai.idr 2>&1 > /dev/null

ISOTODAY=$(date ---rfc-3339=date)
NRUNS=3
TESTDIR="/home/thomas/Documents/01-PhD/idris2-projects/dai-station/tests"
INPUTFILE="cspBenchmarkInput"
# remember we've cd-ed to `src`
OUTFILE="../evaln/${ISOTODAY}-sdf-${NRUNS}.csv"
CSVHEADER='csp,sdf,real-time'

echo ${CSVHEADER} > ${OUTFILE}

for CSP in "4Queens" "6Queens" "8Queens" "10Queens"; do

  CSPPATH="${TESTDIR}/nqueens/${CSP}/${CSP}.csp"

  if [ ! -f ${CSPPATH} ]; then echo "ERROR: Couldn't find '${CSPPATH}'"; exit 1; fi

  # do n runs WITHOUT the SDF heuristic
  IDRCMD=":exec solve \"${CSPPATH}\" Nothing"
  echo "${IDRCMD}" > "${INPUTFILE}"
  for i in $(seq 1 ${NRUNS}); do
    /usr/bin/time -f "${CSP},n,%e" -a -o ${OUTFILE} -- idris2 --no-banner --no-colour -p contrib Dai.idr < "${INPUTFILE}" > /dev/null
  done

  # do n runs WITH the SDF heuristic
  IDRCMD=":exec solve \"${CSPPATH}\" (Just SDF)"
  echo "${IDRCMD}" > "${INPUTFILE}"
  for i in $(seq 1 ${NRUNS}); do
    /usr/bin/time -f "${CSP},y,%e" -a -o ${OUTFILE} -- idris2 --no-banner --no-colour -p contrib Dai.idr < "${INPUTFILE}" > /dev/null
  done

done

for CSP in "2_3" "2_4" "3_9" "3_10"; do

  CSPPATH="${TESTDIR}/langfords/langfords${CSP}/langfords${CSP}.csp"

  if [ ! -f ${CSPPATH} ]; then echo "ERROR: Couldn't find '${CSPPATH}'"; exit 1; fi

  # do n runs WITHOUT the SDF heuristic
  IDRCMD=":exec solve \"${CSPPATH}\" Nothing"
  echo "${IDRCMD}" > "${INPUTFILE}"
  for i in $(seq 1 ${NRUNS}); do
    /usr/bin/time -f "langfords${CSP},n,%e" -a -o ${OUTFILE} -- idris2 --no-banner --no-colour -p contrib Dai.idr < "${INPUTFILE}" > /dev/null
  done

  # do n runs WITH the SDF heuristic
  IDRCMD=":exec solve \"${CSPPATH}\" (Just SDF)"
  echo "${IDRCMD}" > "${INPUTFILE}"
  for i in $(seq 1 ${NRUNS}); do
    /usr/bin/time -f "langfords${CSP},y,%e" -a -o ${OUTFILE} -- idris2 --no-banner --no-colour -p contrib Dai.idr < "${INPUTFILE}" > /dev/null
  done

done

rm benchmarkInput

