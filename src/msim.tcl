global gfn mcrl argc argv last_load_saved client
# set gfn [ lindex $argv 1 ]
set mcrl /ufs/bertl/mutool/bin/mips/mcrl
set title "A simple mCRL simulator:version [lindex $argv 0]"
# $Id: msim.tcl,v 1.2 2004/10/19 14:42:34 uid523 Exp $
set fsize 10
set last_load_saved ""
set client ""
# PROCEDURES

proc strcat {s1 s2} {
    return [format "%s%s" $s1 $s2]
}


proc display-choices {} {
    global rslt fl
    clear-menu
    enable-menu
    if {[catch {step} rslt ]} {
	add-msg "error$rslt"
        return 
	# return -code error
	}
    display-menu $rslt
    if {[winfo exists .t ]} {
         statedisplay [state]
       }
    foreach x $fl {
        add-fmsg $x
    }
    add-lmsg [lastaction]
}

proc do-choice {} {
    global rslt
    if {![info exists rslt ]} { 
	return
    } 
    #if {[catch {selection get} name]} {
    #return
    #}
    # puts stderr [.menu curselection ]
    set sel [ expr [ .menu curselection ] - 1 ]
    if { $sel < 0 || $sel >= [ .menu size ] } { return }
    choice  $sel
    # choice [ lsearch -exact $rslt $name ]
    display-choices
    .redo configure -state disabled
    .undo configure -state active
}

proc do-highlight {} {
    global rslt
    if {![info exists rslt ]} { 
	return
    } 
    set sel [ expr [ .menu curselection ] - 1 ]
    if { $sel < 0 || $sel >= [ .menu size ] } { return }
    # puts stderr [.menu curselection ]
    highlight $sel 
    # choice [ lsearch -exact $rslt $name ]
}

proc init-msg {} {
       text .msg -relief groove -yscrollcommand ".scrollmsg set" -width 40 \
       -height 2 -state disabled
       pack .msg -in .bottom  -side left -expand yes -fill both -padx 0m -pady 0m 
       scrollbar .scrollmsg -command ".msg yview"
       pack .scrollmsg -in .bottom -side right -anchor e -fill y
       # puts stderr [.msg configure ]
}

proc init-lmsg {} {
    # text .middle.msg -relief groove -xscrollcommand ".middle.scroll set" -width 200 \
      # -height 1 -state disabled -wrap none
    text .middle.msg -relief groove -width 200 \
      -height 1 -state disabled -wrap none
    # scrollbar .middle.scroll -orient horizontal -command ".middle.msg xview"
    label .middle.label -text "Last action: "
    pack .middle.label -in .middle  -side left
    # pack .middle.scroll -in .middle -side bottom  -fill x
    pack .middle.msg -in .middle  -side right -expand yes -fill x -padx 0m -pady 0m
    }

proc add-lmsg {s} {
    .middle.msg configure -state normal
    .middle.msg delete 1.0 end 
    .middle.msg insert end "$s\n"
    .middle.msg configure -state disabled
    }

proc add-msg {s} {
    .msg configure -state normal
    .msg insert end "$s\n"
    .msg configure -state disabled
    .msg yview "end -4lines"
    }
    
proc add-fmsg {f} {
    if { [ winfo exists $f ] } {
    $f.msg configure -state normal
    set trm [ $f.entry get ]
    if {[ catch {rewrite $trm } rslt ] } {
	set trm [wm title $f ]
	add-msg "error evaluating $trm $rslt"
	return
    }
    $f.msg delete 1.0 end 
    $f.msg insert end "$rslt"
    $f.msg configure -state disabled
    }
    }
    
proc init-menu {} {
    listbox .menu -relief groove -yscrollcommand ".scroll set" -xscrollcommand ".scrolh set" 
    pack .menu -in .left  -side left -expand yes -fill both -padx 0m -pady 0m
    bind .menu <ButtonPress-1> { do-highlight }
    bind .menu <B1-Motion> { do-highlight  }
    bind .menu <ButtonRelease-1> { do-choice }
    scrollbar .scroll -command ".menu yview" -orient vertical
    pack .scroll -in .left -side right -anchor w -fill y
    scrollbar .scrolh -command ".menu xview" -orient horizontal 
    pack .scrolh -in .left -side bottom -fill x  -before .menu
}

proc enable-menu {} {
       if {[ winfo exists .label ] } { destroy .label }
}

proc statedisplay {compon} {
   .t.menu delete 0 [.t.menu size]
    foreach s $compon {
	.t.menu insert end $s
    }
}

proc statewindowopen {compon} {
    toplevel .t
    wm title .t "state vector"
    wm iconname .t "state vector"
    wm geometry .t 500x300
    wm maxsize .t 1152 900
    button .t.tquit -text "Close" -command { destroy .t; .statevector configure -state active}
    pack .t.tquit -in .t -side right -anchor s 
    listbox .t.menu -relief groove -yscrollcommand ".t.scroll set" -xscrollcommand ".t.scrolh set"
    pack .t.menu -in .t  -side left -expand yes -fill both -padx 0m -pady 0m
    scrollbar .t.scroll -command ".t.menu yview"
    pack .t.scroll -in .t -side right -anchor e -fill y
    scrollbar .t.scrolh -command ".t.menu xview" -orient horizontal
    pack .t.scrolh -in .t -side bottom  -fill x  -before .t.menu
    statedisplay $compon  
}

proc outputwindowopen {} {
    global gfn last_load_saved
    .save configure -state disabled
    set f [ string range $gfn 0 [ expr [ string last ".tbf" $gfn ] - 1 ]]
    set last_load_saved $f
    if {[ catch {savetrace  $last_load_saved} last_load_saved ]} {
        add-msg "err:$last_load_saved"
	return
        }
    add-msg "msg:Trace written on: $last_load_saved"
    .save configure -state active
}

proc handle-input {filename} {
    global last_load_saved
    set last_load_saved $filename
    set length [ loadtrace  $last_load_saved ]
    set length1  [ expr { $length - 1 } ]
    add-msg "msg:Trace of length $length1 read from: $filename"   
    display-choices 
    .redo configure -state active
    .undo configure -state active
    return $length
}

proc inputwindowopen {} {
    global gfn last_load_saved
    .load configure -state disabled
    set f [ string range $gfn 0 [ expr [ string last ".tbf" $gfn ] - 1 ]]
    if { [ file isdirectory "$f.trc" ] } {
      set filename [ tk_getOpenFile -initialdir "$f.trc" -title "Choose trace file" -initialfile $last_load_saved ]
      if { $filename != "" } {
          if { [ catch { handle-input $filename } length ] } {
              .load configure -state active 
              return -code error $length
              }
          if { [ catch { current } err ] } {
             if { $err == 0 } { 
                .redo configure -state disabled
                if { $length == 1 } { .undo configure -state disabled }
                } else {
                .undo configure -state disabled
                }
             }
          }
      } else { add-msg "Directory $f is not found" }
    .load configure -state active
    }
# puts stderr $f
#    if { [ file isdirectory "$f.trc" ] } {
#       set filename [ tk_getOpenFile -initialdir "$f.trc" ]
#       if { $filename != "" } {
#          catch { handle-input $filename }
#.load configure -state active }
#       }
#    } else { add-msg "Directory $f is not found" }
#    .load configure -state active


proc handle-print {} {
    global last_load_saved
    set last_load_saved [ .print.entry get ]
    add-msg [ printtrace  $last_load_saved ] 
    destroy .print  
    # .stateview configure -state active  
}


proc handle_graph {} {
    global client
    if { [ catch { stateview } rslt ] } {
	    add-msg "error$rslt"
    } else { add-msg "rslt$rslt" }
}


proc functionwindowopen {} {
    global fl
    set n [llength $fl ]
    set f ".f$n"
    toplevel $f
    set fl [ linsert $fl 0 $f ]
    wm title $f "term $n"
    wm iconname $f "state function"
    wm geometry $f 500x100
    wm maxsize $f 1152 900
    
    frame $f.top
    frame $f.a
    frame $f.b
    
    button $f.b.tquit -text "Close" -command [ list destroy $f ]
    button $f.a.ok -text "OK" -command [ list add-fmsg $f ]
    
    pack $f.a -in $f -side top  
    pack $f.b -in $f -side bottom
    
    pack  $f.a.ok -in $f.a -side right 
    pack  $f.top -in $f.a -side left
    
    frame $f.down
    pack  $f.b.tquit -in $f.b -side right -anchor n
    pack  $f.down -in $f.b -side left
    
    entry $f.entry -width 200 -relief sunk -bd 2
    label $f.label -text "Enter function:"
    pack  $f.label $f.entry -in $f.top -side left -padx 1m -pady 2m 
    text $f.msg -relief sunken -xscrollcommand "$f.scroll set" -width 200 \
      -height 1 -state disabled -wrap none
    frame $f.down.right
    label $f.label2 -text "Display:"
    pack $f.label2 -in $f.down -side left -padx 1m -pady 2m
    pack $f.down.right -in $f.down -side bottom
    pack $f.msg -in $f.down.right  -side top -expand yes -fill x -padx 0m -pady 0m 
    scrollbar $f.scroll -orient horizontal -command "$f.msg xview"
    pack $f.scroll -in $f.down.right -side bottom  -fill x
    bind  $f.entry  <Return>  [ list add-fmsg $f ]
}

# GLOBAL VARIABLES

global curtbf agecurtbf fl
set fl []
# WINDOW MANAGER

wm geometry . 500x400
wm sizefrom . ""
wm maxsize . 1152 900
wm title . $title
bind . <Enter> { if { "%W"=="." &&  %s == 0  } {
# puts stderr "%W (%x,%y) %b %s %k %T"
                         putstate;  }}


#ROOT WINDOW DIVISION
frame .mbar -bd 2
# frame .dummy -width 10c -height 5c
pack .mbar -side top -fill x 
menubutton .mbar.font -text "Font size" -menu .mbar.font.menu
menu .mbar.font.menu
pack .mbar.font  -side left

.mbar.font.menu add command -label "6 point" -command {set fsize 6;change-fsize} 
.mbar.font.menu add command -label "10 point" -command {set fsize 10;change-fsize} 
.mbar.font.menu add command -label "12 point" -command {set fsize 12;change-fsize} 
.mbar.font.menu add command -label "14 point" -command {set fsize 14;change-fsize} 

frame .bottom
frame .middle
pack .bottom .middle  -side bottom -fill x -ipady 3m

frame .left
pack  .left -side left -expand yes -fill both -padx 2m -pady 2m

frame .right
pack  .right -side right -fill y -padx 2m -pady 2m

frame .right_top
pack .right_top -in .right -side top

frame .right_top_left
frame .right_top_right

pack .right_top_left .right_top_right -in .right_top -side left


label .fileLabel -text "File:"
entry .fileEntry -width 20 -relief sunken -textvariable fn
bind  .fileEntry <Return> {
   if {[catch {sendfilename}]} {return}
   # TBsend "snd-event(restart)"
}

label .dirLabel -text "Directory:"
pack .dirLabel .fileLabel -in .right_top_left -side top -anchor nw

entry .dirEntry -width 20 -relief sunken -textvariable dn
pack .dirEntry .fileEntry -in .right_top_right -side top -anchor nw
bind  .dirEntry <Return> {
   if {[catch {sendfilename}]} {return}
   # TBsend "snd-event(restart)"
}

label  .canvasLabel -text "Menu display"
pack .canvasLabel -in .left -side bottom -padx 0m -pady 0m -anchor nw

init-msg
init-lmsg

# Make menu
init-menu

frame .rright
frame .lleft
frame .mmiddle

button .quit -text "Quit" -command {
   # TBsend "snd-event(terminate)"
   global client
   endstateview
   set client "2"
   destroy .
}

button .statevector -text "State" -command {
    statewindowopen    [ state ]
    .statevector configure -state disabled
}

button .statefunction -text "Term" -command {
    functionwindowopen
    # .statefunction configure -state disabled
}

button .undo -text "Undo" -command {
    global rslt fl
    if {[catch {undo} rslt ]} { 
	.undo configure -state disabled }
    if {[catch {step} rslt ]} {
	add-msg "Error:$rslt" 
	return -code error
	}
    clear-menu
    enable-menu
    display-menu $rslt
    if {[winfo exists .t ]} {
         statedisplay [state]
       }
    foreach x $fl {
        add-fmsg $x
    }
    add-lmsg [lastaction]
    .redo configure -state active
}

button .redo -text "Redo" -command {
    global rslt fl
    if {[catch {redo} rslt ]} { 
	.redo configure -state disabled }
    if {[catch {step} rslt ]} {
	add-msg "Error:$rslt" 
	return -code error
	}
    clear-menu
    enable-menu
    display-menu $rslt
    if {[winfo exists .t ]} {
         statedisplay [state]
       }
    foreach x $fl {
        add-fmsg $x
    }
    add-lmsg [lastaction]
    .undo configure -state active
}

button .load -text "Load" -command {
    inputwindowopen   
}

button .save -text "Save" -command {
    outputwindowopen   
}

button .stateview -text "Graph" -command {
    handle_graph   
    .stateview configure -state disabled
}


proc build-filename {} {
    global gfn dn fn argc argv
    if {$dn != ""} {set gfn [strcat $dn "/" ]} else {set gfn "./"}
    set gfn [ strcat $gfn $fn ]
    if {$argc > 2 && ! [ string match -* [lindex $argv end]] 
	&& ! [ string match -alt [lindex $argv [ expr $argc - 2 ]]]
    } {
	set argv [ lreplace $argv end end $gfn ]
	} else {
	set argv [lappend argv $gfn ]
	set argc [expr $argc + 1 ]
	}
    # set argv ([ expr { $argc -1 } ]) $gfn
    if { [ file exists $gfn ] != 1 && [ file exists "$gfn.tbf" ] != 1 } {
	 add-msg "error:file $gfn cannot be opened"
	 return -code error
        }
    if { [ string last ".tbf" $gfn ] < 0 } {set gfn "$gfn.tbf"}
    if {[ string first / $gfn ]!=0} {
       set pw [pwd]
       set gfn [string range $gfn 0 end]
       set gfn "${pw}/$gfn"
       }
    return -code 0 
    }


proc sendfilename {} { 
    global dn fn gfn curtbf agecurtbf rslt mcrl fl argv argc
    if {[ catch {build-filename} ]} {
	 puts stderr "build error" [expr $agecurtbf]
     }
# puts stderr "filename = $gfn and $curtbf"
    # puts stderr [expr $agecurtbf ]
    if { [ file tail $curtbf ] == [ file tail $gfn ] && ($agecurtbf == [ file mtime $curtbf ])} {
	add-msg "msg:Reset"
	reset
     } else {  
	 add-msg "msg:Restart $gfn"
	 if {[ catch { readlin $argc $argv } err ]} {
	     add-msg "error$err" 
	     set curtbf ""
	     return -code error
	     } else {add-msg "restart$err"}
	 set curtbf $gfn 
	 set agecurtbf [file mtime $gfn]
         endstateview 
         .stateview configure -state active
	}
    if {[catch {step} rslt ]} {
	add-msg "error:$rslt" 
	set curtbf ""
	return -code error
	}
    clear-menu
    enable-menu
    display-menu $rslt
    .load configure -state active
    .save configure -state active
    if {[winfo exists .t ]} {
         statedisplay [state]
       } else {
       .statevector configure -state active
       }
    .statefunction configure -state active
    foreach x $fl {
        add-fmsg $x
    }
    add-lmsg [lastaction]
    .redo configure -state disabled
    .undo configure -state disabled
}

proc alldisable {} { 
    .restart configure -state disabled
    .statevector configure -state disabled
    .statefunction configure -state disabled
    .undo configure -state disabled
    .redo configure -state disabled
    .quit configure -state disabled
    .save configure -state disabled
    .load configure -state disabled
    .dirEntry configure -state disabled
    .fileEntry configure -state disabled
    bind  .fileEntry <Return> {nop}
    bind  .dirEntry  <Return> {nop}
}

proc allenable {} { 
    .restart configure -state active
    .quit configure -state active
    .undo configure -state active
    .redo configure -state active
    .save configure -state active
    .load configure -state active
    .fileEntry configure -state normal
    .dirEntry configure -state normal
    .statevector configure -state active

   bind  .fileEntry <Return> {
     if {[catch sendfilename]} {return}
     # TBsend "snd-event(restart)"
     }

   bind  .dirEntry <Return> {
     if {[catch sendfilename]} {return}
     # TBsend "snd-event(restart)" }
}

button .restart -text "Start" -command {
   clear-menu
   if {[catch sendfilename]} {return}
}

pack  .quit -in .rright -side bottom  -padx 1m -pady 1m \
	-anchor s -fill x
pack  .load -in .mmiddle -side bottom  -padx 1m -pady 1m \
	-anchor s -fill x
pack  .restart -in .lleft -side bottom -padx 1m -pady 1m \
	-anchor s -fill x        
pack  .undo -in .lleft -side bottom  -padx 1m -pady 1m \
	-anchor s -fill x
pack  .save -in .mmiddle -side bottom  -padx 1m -pady 1m \
	-anchor s -fill x
pack  .stateview -in .mmiddle -side bottom  -padx 1m -pady 1m \
	-anchor s -fill x
pack  .redo -in .rright -side bottom  -padx 1m -pady 1m \
	-anchor s -fill x
pack  .statefunction -in .lleft -side bottom -padx 1m -pady 1m \
	-anchor s -fill x
pack  .statevector -in .rright -side bottom  -padx 1m -pady 1m \
	-anchor s -fill x

pack .rright -in .right -side right -fill y
pack .mmiddle -in .right -side right -fill y
pack .lleft -in .right -side right -fill y

.statefunction configure -state disabled
.statevector configure -state disabled
.undo configure -state disabled
.redo configure -state disabled
.load configure -state disabled
.save configure -state disabled
.stateview configure -state disabled


proc display {str} {.menu insert end $str}

proc display-menu {str} {
  if {[llength $str] == 0} {
	label .label -text "deadlock"
	pack .label -in .menu  -side left -expand yes \
	    -fill both -padx 0m -pady 0m
	return;
  }
  if {[llength $str] == 1 && $str == "Qterminated"} {
      label .label -text "terminated"
      pack .label -in .menu  -side left -expand yes \
	  -fill both -padx 0m -pady 0m
      return;
      } 
  .menu insert end "____________________________________________________________"
  foreach s $str {
      display $s
      }
  .menu insert end ""
}

proc clear-menu {} {
    .menu delete 0 [.menu size]
}
 
proc s-termination {} {
   # clear-menu
   # display-menu "Succesfull termination\n"
}

proc change-fsize {} {
    global fsize
    set aap [ list Helvetica  [expr $fsize ]  normal ]
    if {[catch {.menu configure -font  $aap}]} {} 
}

# FILE HANDLING

# set gfn "./1394-fin.tbf"
set curtbf  ""
set agecurtbf 0

if {$argc > 0 && ! [ string match -* [lindex $argv end]] 
	&& 
	! [ string match -alt [lindex $argv [ expr $argc - 2 ]]]
} {
    # set gfn   [ lindex $argv   [ expr { $argc - 1 } ] ] 
    set gfn   [ lindex $argv end ] 
    } else { 
    set argv [lappend argv $gfn ]
    set argc [expr $argc + 1 ]
    }
set dn  [ file dirname $gfn ]
set fn  [ file tail $gfn ]
if {[catch {build-filename}]} {} 

set aap [ list Helvetica  [ expr $fsize ]  normal ]
if {[catch {.menu configure -font  $aap}]} {} 
bind .mbar.font.menu <ButtonRelease> { change-fsize }

# clear-menu
# BindSSL .menu

while {1} {
	tkwait variable client
        # puts stderr "aap:$client\n"
        if {$client=="2"} {
           exit;
           }
        if {$client=="1"} {
           puts stdout "Client started"
           }
        if {$client=="" && [winfo exists .stateview] } {
           .stateview configure -state active
           }
}
