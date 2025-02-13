OPENQASM 2.0;
include "qelib1.inc";

qreg sites[2];
reset sites;

rx(exp(5)) sites[0];

 u(1, pi, 1) sites[1];

creg results[2];
measure sites -> results;