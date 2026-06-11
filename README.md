# Quantum-computing-in-Lean4
Quantum-computing-in-Lean4 has formalized some quantum algorithm including Deutsch-Jozsa algorithm,Bernstein-Vazirani algorithm, Simon's algorithm and Grover's algorithm in Lean4.For algorithms that require multiple runs, we verify the expected output of a single run.


## Documentation

The library is organised into the following core modules:

| Module | Description |
|--------|-------------|
| `Qcircuits/Basic` | Fundamental definitions: qubits, quantum gates. |
| `Qcircuits/Laws` | Algebraic laws for gate equivalences. |
| `Qcircuits/Strategies` | Rewriting strategies for equational reasoning. |
| `Qcircuits/Density` | Density matrix formalism for pure states. |
| `Qcircuits/Equiv` | Equivalence relations between circuits. |
| `Qcircuits/ObsEquiv` | Observational equivalence. |
| `Qcircuits/NQubit` | Generic n-qubit and inductive constructions for scalable verification. |
| `Qcircuits/DeutschJozsa` | Verified Deutsch‑Jozsa algorithm. |
| `Qcircuits/BernsteinVazirani` | Verified Bernstein‑Vazirani algorithm. |
| `Qcircuits/Simon` | Verified Simon’s period‑finding algorithm(one run). |
| `Qcircuits/Grover` | Verified Grover’s search algorithm. |
| `Qcircuits/ExtendedGates` | More gates are making. |


## AI Assistance

AI tools have assisted with proving process. Domain contributors remain responsible for reviewing definitions and proofs.


## Contributors (alphabetical by surname)

**Contributors:** :


## References

- Hidary, J. D. (2021). *Quantum Computing: An Applied Approach* (2nd ed.). Springer. Integrates foundations with practical coding approaches.
- Shi, W., Cao, Q., Deng, Y., Jiang, H., & Feng, Y. (2021). Symbolic Reasoning About Quantum Circuits in Coq. *Journal of Computer Science and Technology*, 36, 1291–1306. https://doi.org/10.1007/s11390-021-1637-9
- inQWIRE team. SQIR: A Small Quantum Intermediate Representation (Coq formalisation). https://github.com/inQWIRE/SQIR. Appears in: Hietala, K., Rand, R., Hung, S.-H., Wu, X., & Hicks, M. (2021). A Verified Optimizer for Quantum Circuits. *POPL 2021*.
- 邓玉欣, & 徐鸣. (2026). 量子计算导论. 清华大学出版社. ISBN: 9787302710066