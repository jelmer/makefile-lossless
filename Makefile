ifneq = blar
blah = foo

foo --bar:
	echo $(blah)

all:
	echo $(ifneq)
