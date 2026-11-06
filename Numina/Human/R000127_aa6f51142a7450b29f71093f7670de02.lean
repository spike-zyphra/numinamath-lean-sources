import Mathlib

/- a) \(\begin{pmatrix} 1 & 1 & 0 \\ 1 & 0 & 1 \\ 0 & 1 & 1 \end{pmatrix}\)-/
theorem number_theory_4734_1 {A : Matrix (Fin 3) (Fin 3) (ZMod 7)}
    (hA : A = !![1, 1, 0; 1, 0, 1; 0, 1, 1]) :
    A * !![4, 4, 3; 4, 3, 4; 3, 4, 4] = 1 := by
  -- verify by computation
  rw [hA]
  native_decide

/- b) \(\begin{pmatrix} 1 & 2 & 3 \\ 1 & 2 & 5 \\ 1 & 4 & 6 \end{pmatrix}\)-/
theorem number_theory_4734_2 {A : Matrix (Fin 3) (Fin 3) (ZMod 7)}
    (hA : A = !![1, 2, 3; 1, 2, 5; 1, 4, 6]) :
    A * !![2, 0, 6; 2, 1, 4; 3, 4, 0] = 1 := by
  -- verify by computation
  rw [hA]
  native_decide

/- c) \(\begin{pmatrix} 1 & 1 & 1 & 0 \\ 1 & 1 & 0 & 1 \\ 1 & 0 & 1 & 1 \\ 0 & 1 & 1 & 1 \end{pmatrix}\)-/
theorem number_theory_4734_3 {A : Matrix (Fin 4) (Fin 4) (ZMod 7)}
    (hA : A = !![1, 1, 1, 0; 1, 1, 0, 1; 1, 0, 1, 1; 0, 1, 1, 1]) :
    A * !![5, 5, 5, 4; 5, 5, 4, 5; 5, 4, 5, 5; 4, 5, 5, 5] = 1 := by
  -- verify by computation
  rw [hA]
  native_decide
