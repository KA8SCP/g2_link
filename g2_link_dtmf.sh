#!/bin/bash

# This script finds files in the /tmp  directory
#    The files have a name like x_mod_DTMF_NOTIFY, where x is one of 0 1 2
#       0=A module,  
#       1=B module,  
#       2=C module
#    The contents of these files can be as follows:

# Example:  73     will unlink local module
# Example:  #02102   will link local module to reflector XRF021 B
# Example:  *01601   will link local module to reflector REF016 A
# Example:  D00126   will link local module to reflector DCS001 Z
# Example:  99      will report status

# The netcat command
NC=`which nc`
if [ -z $NC ] ; then
        echo Could not locate nc command, on some systems is netcat
        exit 1
fi

# g2_link listens on this command port
# This is the same value in g2_link.cfg
COMMAND_PORT=30003

# g2_link opens its command port on 0.0.0.0
#   so the COMMAND_IP here must be 127.0.0.1
COMMAND_IP=127.0.0.1

# We set this to spaces, it will be set later
LUSER="        "

cd /tmp
echo started at `date`

while [ 1 ]
do
   for i in `ls ?_mod_DTMF_NOTIFY 2>/dev/null`
   do
      echo found file $i at `date`
      x=${i:0:1}
      if [ "$x" = "0" ] ; then
         LOCAL_BAND=A
      elif [ "$x" = "1" ] ; then
         LOCAL_BAND=B
      elif [ "$x" = "2" ] ; then
         LOCAL_BAND=C
      else
         LOCAL_BAND=garbage
      fi

      if [[ "$LOCAL_BAND" == "garbage" ]]
      then
          echo garbage value for local band
      else
         CMD=`head -n 1 $i 2>/dev/null`
         LUSER=`tail -n 1 $i 2>/dev/null`
         echo "... with these contents: " $CMD " " $LUSER
         if [ "$CMD" = "73" ] ; then
            echo Unlinking local band $LOCAL_BAND requested by $LUSER
$NC -u -w 2 $COMMAND_IP $COMMAND_PORT << EOF
um $LOCAL_BAND
EOF
            echo
         elif [ "$CMD" = "99" ] ; then
            echo Link Status on local band $LOCAL_BAND requested by $LUSER
$NC -u -w 2 $COMMAND_IP $COMMAND_PORT << EOF
in $LOCAL_BAND
EOF
            echo
         else
            LEN=${#CMD}
            if [ "$LEN" = "6" ] ; then
               PFX=${CMD:0:1}
               REMOTE_NODE=${CMD:1:3}
               REMOTE_BAND=${CMD:4:2}

               if [ "$REMOTE_BAND" = "01" ] ; then
                  REMOTE_BAND=A
               elif [ "$REMOTE_BAND" = "02" ] ; then
                  REMOTE_BAND=B
               elif [ "$REMOTE_BAND" = "03" ] ; then
                  REMOTE_BAND=C
               elif [ "$REMOTE_BAND" = "04" ] ; then
                  REMOTE_BAND=D
               elif [ "$REMOTE_BAND" = "05" ] ; then
                  REMOTE_BAND=E
               elif [ "$REMOTE_BAND" = "06" ] ; then
                  REMOTE_BAND=F
               elif [ "$REMOTE_BAND" = "07" ] ; then
                  REMOTE_BAND=G
               elif [ "$REMOTE_BAND" = "08" ] ; then
                  REMOTE_BAND=H
               elif [ "$REMOTE_BAND" = "09" ] ; then
                  REMOTE_BAND=I
               elif [ "$REMOTE_BAND" = "10" ] ; then
                  REMOTE_BAND=J
               elif [ "$REMOTE_BAND" = "11" ] ; then
                  REMOTE_BAND=K
               elif [ "$REMOTE_BAND" = "12" ] ; then
                  REMOTE_BAND=L
               elif [ "$REMOTE_BAND" = "13" ] ; then
                  REMOTE_BAND=M
               elif [ "$REMOTE_BAND" = "14" ] ; then
                  REMOTE_BAND=N
               elif [ "$REMOTE_BAND" = "15" ] ; then
                  REMOTE_BAND=O
               elif [ "$REMOTE_BAND" = "16" ] ; then
                  REMOTE_BAND=P
               elif [ "$REMOTE_BAND" = "17" ] ; then
                  REMOTE_BAND=Q
               elif [ "$REMOTE_BAND" = "18" ] ; then
                  REMOTE_BAND=R
               elif [ "$REMOTE_BAND" = "19" ] ; then
                  REMOTE_BAND=S
               elif [ "$REMOTE_BAND" = "20" ] ; then
                  REMOTE_BAND=T
               elif [ "$REMOTE_BAND" = "21" ] ; then
                  REMOTE_BAND=U
               elif [ "$REMOTE_BAND" = "22" ] ; then
                  REMOTE_BAND=V
               elif [ "$REMOTE_BAND" = "23" ] ; then
                  REMOTE_BAND=W
               elif [ "$REMOTE_BAND" = "24" ] ; then
                  REMOTE_BAND=X
               elif [ "$REMOTE_BAND" = "25" ] ; then
                  REMOTE_BAND=Y
               elif [ "$REMOTE_BAND" = "26" ] ; then
                  REMOTE_BAND=Z
               else
                  REMOTE_BAND=Z
               fi

               if [ "$PFX" = "#" ] ; then
                  RMT=XRF
               elif [ "$PFX" = "D" ] ; then
                  RMT=DCS
               else
                  RMT=garbage
               fi

               if [[ "$RMT" == "garbage" ]]
               then
                  echo garbage value in prefix
               else
                  echo linking local band $LOCAL_BAND to remote node ${RMT}${REMOTE_NODE} $REMOTE_BAND requested by $LUSER
$NC -u -w 2 $COMMAND_IP $COMMAND_PORT << EOF
lm ${LOCAL_BAND}${RMT}${REMOTE_NODE}${REMOTE_BAND}
EOF
                  echo
               fi
            fi
         fi
      fi
      rm -f $i
   done
   sleep 2
done

exit 0

