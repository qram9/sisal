for file in *.sis; do
  ../main.byte $file > $file.out || exit -1
done
