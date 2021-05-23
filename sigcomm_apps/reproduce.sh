# compile the p4 to tofino if the SDE exists.
if [ -d "/home/vagrant/bf-sde-9.5.0" ]
then
    export SDE=/home/vagrant/bf-sde-9.5.0
    export SDE_INSTALL=/home/vagrant/bf-sde-9.5.0/install
    export PATH=$PATH:$SDE_INSTALL/bin
    cd ~/lucid/sigcomm_apps
    make p4
    make tofino
    make stats
else
    cd ~/lucid/sigcomm_apps
    make p4
    make stats
fi

