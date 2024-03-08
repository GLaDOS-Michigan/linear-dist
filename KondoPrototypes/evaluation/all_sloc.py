import csv
import os
from sloc import count_sloc_between

CSV_FILE = "protocols.csv"
ROOT_PATH = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/messageInvariantPrototypes"
OUTPUT_PATH = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/messageInvariantPrototypes/evaluation/sloc.csv"

def analyze_protocol(file_path):
    with open(file_path, 'r') as csvfile:
        csv_reader = csv.reader(csvfile)
        res = []
        # async_full is the case where we use triggers
        res.append("protocol,sync_spec,total_sync_proof,total_async_proof,total_async_full")

        for row in csv_reader:
            protocol = row[0]

            async_proof_file_path = f"{ROOT_PATH}/{protocol}/automate/applicationProof.dfy"
            async_full_proof_file_path = f"{ROOT_PATH}/{protocol}/automate_full/applicationProof.dfy"
            sync_proof_file_path = f"{ROOT_PATH}/{protocol}/centralized/applicationProof.dfy"

            async_sloc = count_sloc_between(async_proof_file_path, 1, 1000000)
            sync_sloc = count_sloc_between(sync_proof_file_path, 1, 1000000)
            
            # if automate_full path exists, then we compute SLOC (minus triggers)
            if os.path.isfile(async_full_proof_file_path):
                async_full_sloc = count_sloc_between(async_full_proof_file_path, 1, 1000000)
            else:
                async_full_sloc = -1  # invalid

            spec_file_paths = [
                f"{ROOT_PATH}/{protocol}/hosts.dfy",
                f"{ROOT_PATH}/{protocol}/types.dfy",
                f"{ROOT_PATH}/{protocol}/centralized/spec.dfy",
                f"{ROOT_PATH}/{protocol}/centralized/system.dfy"
            ]
            spec_sloc = 0
            for fp in spec_file_paths:
                spec_sloc += count_sloc_between(fp, 1, 1000000)

            line = f"{protocol},{spec_sloc},{sync_sloc},{async_sloc},{async_full_sloc}"
            res.append(line)
    write_to_file(OUTPUT_PATH, "\n".join(res))


def write_to_file(file_path, content):
    with open(file_path, 'w') as file:
        file.write(content)


def main():
    analyze_protocol(CSV_FILE)

if __name__ == "__main__":
    main()