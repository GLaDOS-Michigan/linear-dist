# Readme

No atomic receive-and-send in the same step.
Compared to monotonic_no-recv-send, this version uses a single option for `nominee` field
in Host state, compared to using a sequence. As a result, the proof here should match the 
centralized version.
