#!/usr/bin/env bash
source venv/bin/activate
python -m sloth.benchmarks.benchmarks "$@"
deactivate
