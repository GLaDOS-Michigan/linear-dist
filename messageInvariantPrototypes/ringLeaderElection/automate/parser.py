import collections
import re

SEND_PREDICATE_KEYWORD = "sendPredicate"

class Module:
    def __init__(self, raw):
        self.raw_string = raw
        self.name = "mod_name"
        self.send_predicates = []
    
    def add_predicate(self, new_pred):
        self.send_predicates.append(new_pred)

    def __str__(self):
        res = []
        res.append("module " + self.name + ":")
        if len(self.send_predicates) == 0:
            res.append("   " + "no send predicates")
        
        for sp in self.send_predicates:
            res.append("   " + sp.__str__())
        res.append("")
        return "\n".join(res)

class SendPredicate:
    def __init__(self, name = "sp_name", hosts_field = "hosts"):
        self.name = name
        self.hosts_field = hosts_field

    def __str__(self):
        return self.name + ": " + self.host_field

"""Returns Module list"""
def parse(hf):
    def skip_line(line):
        return line.strip() == "" or "include" in line
    
    res = []
    curr_module = []
    open_braces = 0
    for line in hf:
        if skip_line(line) and open_braces == 0:
            continue
        all_counts = collections.Counter(line)
        open_braces += all_counts["{"]
        open_braces -= all_counts["}"]
        curr_module.append(line)
        if open_braces == 0:
            res.append(parse_module(curr_module))
            # reset
            curr_module = []
            open_braces = 0
    return res

"""Returns Module"""
def parse_module(module_lines):
    res = Module("".join(module_lines))

    # Scan for Send Predicates
    lines_iter = iter(module_lines)
    line = next(lines_iter)
    res.name = re.split(' |\{', line)[1]
    try:
        while True:
            line = next(lines_iter)
            # Found a Send Predicate
            if SEND_PREDICATE_KEYWORD in line:
                sp = SendPredicate()
                sp.host_field = re.sub(" |[^0-9a-zA-Z\s]+", "", line.split(":")[1]).strip()
                while "ghost predicate" not in line:
                    line = next(lines_iter)
                sp.name = re.split(' |\(', line)[4].strip()
                res.add_predicate(sp)
    except StopIteration:
        pass
    return res
