import Mathlib

/- Find the units digit of the following:  \begin{align*}
& (972 - 268)(973 - 267)(974 - 266) \\
&\qquad+ (968 - 272)(967 - 273)(966 - 274) - (999 - 222)^3
\end{align*} -/
theorem number_theory_22832 : ((972 - 268) * (973 - 267) * (974 - 266) +
    (968 - 272) * (967 - 273) * (966 - 274) - (999 - 222)^3) % 10 = 7 := by 
  decide