import collections
import re
import sys
import msgInv

SEND_PREDICATE_KEYWORD = "sendPredicate"

"""Returns Module list"""
def parse(hosts_file):
    def skip_line(line):
        return line.strip() == "" or "include" in line
    
    res = []
    curr_module = []
    open_braces = 0
    for line in hosts_file:
        if open_braces == 0 and skip_line(line):
            continue
        all_counts = collections.Counter(line)
        open_braces += all_counts["{"]
        open_braces -= all_counts["}"]
        curr_module.append(line)
        if open_braces == 0:
            res.append(parse_module(curr_module))
             # Reset after parsing each module
            curr_module = []
    return res

"""Returns Module"""
def parse_module(module_lines: [str]):
    module = msgInv.Module("".join(module_lines))

    # Scan for Send Predicates
    lines_iter = iter(module_lines)
    line = next(lines_iter)
    module.name = re.split(' |\{', line)[1]
    while True:
        try:
            line = next(lines_iter)
            # Found a Send Predicate
            if SEND_PREDICATE_KEYWORD in line:
                predicate = msgInv.SendPredicate(module.name)
                attributes_string = line.split(":")[1]
                predicate.host_field = attributes_string.split(",")[0].strip()
                predicate.msg_cons = attributes_string.split(",")[1].strip()
                while "ghost predicate" not in line:
                    line = next(lines_iter)
                predicate.name = re.split(" |\(", line)[4].strip()
                module.add_predicate(predicate)
        except StopIteration:
            break
    return module

def main():
    args = sys.argv[1:]
    host_file = args[0]
    with open(host_file, "r+") as host_file:
        modules = parse(host_file)
        msg_inv_file = msgInv.MessageInvariantsFile(modules)
        print(msg_inv_file.to_dafny_string())
    
if __name__ == "__main__":
    main()