#!/usr/bin/env bash
source venv/bin/activate
python -m sloth.sloth "$@"
deactivate
