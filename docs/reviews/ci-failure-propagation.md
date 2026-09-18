# CI failure propagation review

**Priority:** high; affects whether future regressions can be reported as green.

The baseline workflow piped its model, native, and Loom checks through `tee` without specifying a shell. The log for run `35318006244` records `shell: /usr/bin/bash -e {0}`. Under that invocation, the status of `failing-check | tee log` is normally the status of `tee`, so a failed check can leave the step green. The contents of that historical run's logs showed the expected successful test counts; this finding does not retroactively claim those checks failed.

Reproducer, run in a disposable directory:

```sh
false | tee evidence.log
printf 'step continued\n'
```

`bash -e step.sh` exited 0 and printed `step continued`. `bash --noprofile --norc -eo pipefail step.sh` exited 1 without reaching the print. This matches GitHub's distinction between the implicit shell and explicitly selected Bash. See [GitHub's workflow shell documentation](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idstepsshell).

The workflow now specifies `defaults.run.shell: bash`. Both jobs also execute a deliberately failing producer through `tee` and fail the job if the pipeline is incorrectly treated as successful. That probe tests the actual CI shell context, so removing the default later cannot silently restore the hole.

This guard complements the proof/audit negative tests and native missing-store mutation. Successful commands remain necessary; correct failure propagation is a separate property.
