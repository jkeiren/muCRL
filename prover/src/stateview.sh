#!/bin/sh 
java -Xmx500m -cp ../java/stateview.jar:../java/aterm.jar:$1/stateview.jar:$1/aterm.jar:$1/grappa.jar  stateview.Stateview  $2
