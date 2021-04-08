# for d in ice_oracle*/ ; do
# echo $d
# cd $d
# make
# g++ positive_unroll.cpp -o positive_unroll
# export PATH=$(pwd):$PATH
# echo "running cegis"
# #cp cegis_out ice_out
# timeout 3600 time emu minor2.sl --cvc4 --grammar --constants > cegis_out 2>&1
# echo "runnign ice"
# timeout 3600 time emu ice-minor2.sl --cvc4 --grammar --constants > ice_out 2>&1
# cd ..
# done;

echo iceoracle6
cd ice_oracle6
make
g++ positive_unroll.cpp -o positive_unroll
export PATH=$(pwd):$PATH
echo "running cegis"
#cp cegis_out ice_out
timeout 360 time emu minor2.sl --cvc4 --grammar --constants > cegis_out 2>&1
echo "runnign ice"
timeout 360 time emu ice-minor2.sl --cvc4 --grammar --constants > ice_out 2>&1
cd ..

echo iceoracle7
cd ice_oracle7
make
g++ positive_unroll.cpp -o positive_unroll
export PATH=$(pwd):$PATH
echo "running cegis"
#cp cegis_out ice_out
timeout 360 time emu minor2.sl --cvc4 --grammar --constants > cegis_out 2>&1
echo "runnign ice"
timeout 360 time emu ice-minor2.sl --cvc4 --grammar --constants > ice_out 2>&1
cd ..