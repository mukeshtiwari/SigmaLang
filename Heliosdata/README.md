# Helios election data

The published transcripts of two IACR elections, as fetched from the
Helios server. They are kept here so the verifier can be run without
another repository checked out alongside.

| file | election | ballots | trustees | candidates |
| --- | --- | --- | --- | --- |
| `IACR2024.txt` | [2024](https://vote.heliosvoting.org/helios/elections/a447fe8a-80c8-11ef-923c-7aae6cdba09d) | 932 | 3 | 7 |
| `IACR2023.txt` | [2023](https://vote.heliosvoting.org/helios/elections/c3dd2456-6a89-11ee-b981-bad8622d1122) | 848 | 3 | 6 |

Both use the same 2048-bit group; only the election public key differs.

The format is three sections separated by semicolons: the ballots, one
JSON object per line; then the trustees, as a JSON array carrying their
public keys, decryption factors, decryption proofs and key proofs; then
the published tally.

Fetched with the tool in the SigmaProtocol repository, which asks the
Helios server for each voter's last ballot, so the deduplication these
files reflect was done by the server rather than by any verifier.

To check one:

    ./_build/default/Executable/Heliosrealcode/main.exe Heliosdata/IACR2024.txt
