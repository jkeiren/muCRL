#!/usr/bin/python

from optparse import OptionParser

def transform(input_filename, output_filename):
  input_file = open(input_filename, 'r')
  output_file = open(output_filename, 'w')
  
  for line in input_file:
    if 'd' in line:
      print "Removing des line"
    else:
      output_file.write(line)
  
  input_file.close()
  output_file.close()
  
def main():
  usage = "usage: %prog INPUT OUTPUT"
  option_parser = OptionParser(usage)
  (options, args) = option_parser.parse_args()

  if len(args) != 2:
    option_parser.print_help()
  else:
    transform(args[0],args[1])

if __name__ == "__main__":
  main()

