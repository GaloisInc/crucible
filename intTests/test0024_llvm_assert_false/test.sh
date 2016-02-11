$SAW test.saw
RES=$?
echo $RES
if [ $RES -eq 0 ] ; then
    exit 1
else
    exit 0
fi
