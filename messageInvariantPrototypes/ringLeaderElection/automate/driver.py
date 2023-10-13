import parser
import sys

def main():
    args = sys.argv[1:]
    host_file = args[0]
    with open(host_file, "r+") as hf:
        modules = parser.parse(hf)
        for m in modules:
            print(m)
    
if __name__ == "__main__":
    main()