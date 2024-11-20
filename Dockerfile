# This file was used in the evaluation part of a paper.
# As the development of the code, the dockerfile might be broken.

# syntax=docker/dockerfile:1
FROM ubuntu:22.04
# docker build -t omt:latest .
# docker run -it omt:latest
# change apt source
RUN sed -i s@/archive.ubuntu.com/@/mirrors.zju.edu.cn/@g /etc/apt/sources.list
RUN apt-get clean
RUN apt-get update
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip \
    git \
    vim \
    tmux \
    wget \
    curl \
    # for Yices2
    libgmp-dev\
    swig \
    cmake \
    autoconf \
    gperf \
    libboost-all-dev \
    build-essential \
    default-jre \
    zip \
    # for Bitwuzla
    ninja-build \
    pkg-config

RUN mkdir omt
COPY . /omt

# install omt package requirements
RUN pip install -r /omt/requirements.txt

# install cudd library
RUN git clone -b 3val https://github.com/martinjonas/cudd.git
RUN cd cudd && ./configure --enable-silent-rules --enable-obj --enable-shared && make -j4 && make install
# install antlr
RUN wget https://www.antlr.org/download/antlr-4.11.1-complete.jar -P /usr/share/java
WORKDIR /omt/bin_solvers/
RUN chmod +x /omt/bin_solvers/download.sh
RUN /omt/bin_solvers/download.sh

WORKDIR /