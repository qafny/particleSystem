We have the above qblue benchmark set (well, we should have more, maybe I can ask Yongxin Yao to get one or two real-world program for Pauli string results).

First, we should have a table listing what is being simulated for each of the program. I can work on this.

Second, we should list the compilation time for running each benchmark programs. We might be able to classify these programs as small, medium or large, and then show that the average compilation time for each group.

Third, We will show that our system is effective and scalable in dealing with different cases. So, we will show the compilation time for setting up several error-bounds and several time (currently, we are thinking of the error-bounds to be 10^-3 and 10^-1, and the time to be 0.1, 0.5 and 1). This is more of comparing to ourselves, and demonstrate that the scalability.

Fourth, we can also compare running our system against previous work. We will compare with 2QAN and Paulihereal, via the same benchmark set. We might be able to show that they are not scalable or effective. The main comparison here is to compare the resource estimates, such as gate/qubit counts.

Fifth, we can also compare ourselves. We have four different trotter based algorithms, instead of doing optimization, for different scenario (small, medium, large programs, and different error bounds or time), we will show the resource estimates of different trotter algorithms.

Sixth, we can also compare the trottered based algorithms vs LCU group. We have implemented the Taylor series algorithm for LCU, we will show that trotted algorithm makes a lot more sense (in terms of resource estimates) against these LCU group. This one can be postponed if we think it is not necessary and we do not have time.

We have nother evaluation for the sixth here. We have two ways of compiling our circuit: analog vs digital, we can easily compare the performance of the two.