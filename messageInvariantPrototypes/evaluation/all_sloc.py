import csv
from sloc import count_sloc_between

CSV_FILE = "protocols.csv"
ROOT_PATH = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/messageInvariantPrototypes"
OUTPUT_PATH = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/messageInvariantPrototypes/evaluation/sloc.csv"

def analyze_protocol(file_path):
    with open(file_path, 'r') as csvfile:
        csv_reader = csv.reader(csvfile)
        res = []
        res.append("protocol,sync_spec,total_sync_proof,total_async_proof")

        for row in csv_reader:
            protocol = row[0]

            async_roof_file_path = f"{ROOT_PATH}/{protocol}/automate/applicationProof.dfy"
            sync_proof_file_path = f"{ROOT_PATH}/{protocol}/centralized/applicationProof.dfy"
            async_sloc = count_sloc_between(async_roof_file_path, 1, 1000000)
            sync_sloc = count_sloc_between(sync_proof_file_path, 1, 1000000)

            spec_file_paths = [
                f"{ROOT_PATH}/{protocol}/hosts.dfy",
                f"{ROOT_PATH}/{protocol}/types.dfy",
                f"{ROOT_PATH}/{protocol}/centralized/spec.dfy",
                f"{ROOT_PATH}/{protocol}/centralized/system.dfy"
            ]
            spec_sloc = 0
            for fp in spec_file_paths:
                spec_sloc += count_sloc_between(fp, 1, 1000000)

            line = f"{protocol},{spec_sloc},{sync_sloc},{async_sloc}"
            res.append(line)
    write_to_file(OUTPUT_PATH, "\n".join(res))


def write_to_file(file_path, content):
    with open(file_path, 'w') as file:
        file.write(content)


def main():
    analyze_protocol(CSV_FILE)

if __name__ == "__main__":
    main()