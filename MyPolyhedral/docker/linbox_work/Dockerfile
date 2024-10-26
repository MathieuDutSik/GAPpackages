# to do anything with Docker:
#  docker build -t linbox_work:build-env .
#  docker run -i -t linbox_work:build-env  /bin/bash

# Set the base image
FROM ubuntu:22.04

# Dockerfile maintainer (original author: Mathieu Dutour Sikiric)
MAINTAINER Mathieu Dutour Sikiric <mathieu.dutour@gmail.com>


# Install Ubuntu packages
RUN apt-get update -y
RUN apt-get install -y libgdbm-dev libsnappy-dev make pkg-config rlwrap screen software-properties-common sudo unzip zlib1g-dev zsh
RUN apt-get install -y wget emacs joe
RUN apt-get install -y g++ gcc gfortran
RUN apt-get install -y git cmake
RUN apt-get install -y m4
RUN apt-get install -y libboost-all-dev


# GMP
RUN apt-get install -y libgmp-dev
ENV GMP_INCDIR "/usr/include"
ENV GMP_CXX_LINK "-lm -lgmp -lgmpxx"


# GSL
RUN apt-get install -y libgsl-dev


# Required for LINBOX
RUN apt-get install -y autoconf libblas-dev libntl-dev csh


# mpfrc++
RUN apt-get install -y libmpfr-dev
ENV MPFR_INCDIR /usr/include
ENV MPFR_LINK "-lmpfr"
ENV MPREAL_INCLUDE "-I/opt/mpfrc++-3.6.2"



# Installing gap
WORKDIR /opt
RUN wget https://www.gap-system.org/pub/gap/gap-4.11/tar.gz/gap-4.11.0.tar.gz
RUN tar -vxzf gap-4.11.0.tar.gz && cd gap-4.11.0 && ./configure && make
RUN cd gap-4.11.0/pkg/grape-4.8.3 && ./configure ../.. && make
#RUN cd gap-4.11.0/pkg/CaratInterface && tar -vxzf carat.tgz && cd carat && cat Makefile | grep -v Gmp > Makefile.tmp && mv Makefile.tmp Makefile && make


# polyhedral GAP code compilation
RUN mkdir listlink
WORKDIR /opt/listlink


# Downloading the polyhedral code
RUN cd /opt/gap-4.11.0/pkg && wget http://mathieudutour.altervista.org/Polyhedral/polyhedral.tar.bz2
RUN cd /opt/gap-4.11.0/pkg && bzip2 -d polyhedral.tar.bz2
RUN cd /opt/gap-4.11.0/pkg && tar -vxf polyhedral.tar


