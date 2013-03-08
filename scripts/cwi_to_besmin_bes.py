#!/usr/bin/python

from optparse import OptionParser

def transform(input_filename, output_filename):
  input_file = open(input_filename, 'r')
  content = input_file.read()
  input_file.close()

  content = content.strip()
  content = content.strip('\n')
  nodes = len(content.split('\n'))
  newcontent = content.replace("&", "&\n")
  newcontent = newcontent.replace("|", "|\n")
  newcontent = newcontent.strip()
  edges = len(newcontent.split('\n'))
  
  output_file = open(output_filename, 'w')
  output_file.write("des(0,%d,%d)\n" % (edges, nodes))
  output_file.write(content)
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

