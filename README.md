Modelling compiler passes as games and proving monotone improvement and worst-case performance bounds on them using smoothness proofs. Trying this on an inline-expansion pass for now. This project is very much a work-in-progress. 

Projects that have informed this idea a lot:
- The IR is based on Clight from CompCert, and the inlining proofs reference techniques from CompCerts backend verification project: https://compcert.org/
- Smoothness Proof: https://www.math.uwaterloo.ca/~cswamy/courses/co759/agt-material/christodoulouk-atcongstoc.pdf
- AGT formalizations in Rocq (some code from this project has been copied into my project): https://par.nsf.gov/servlets/purl/10050159

Proofs (not theorem statements or definitions) were developed with LLMs. These changes are mostly localized in `BackwardSim.v` and `CongestionGame.v`. `InliningProof.v` was mostly proven by hand (by me). 
