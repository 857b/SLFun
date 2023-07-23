#!/usr/bin/sed

s/^Tactic call \(.*\) ran for \(.*\) secs.*$/\1:\2/
s/^Finished transaction in \(.*\) secs.*$/qed:\1/
s/^COQC \(.*\)s$/coqc:\1/
