import Mathlib

/- a) \(\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}\)-/
theorem number_theory_4733_1 {A : Matrix (Fin 2) (Fin 2) (ZMod 5)} (hA : A = !![0, 1; 1, 0]) :
    A * !![0, 1; 1, 0] = 1 := by
  -- verify by computation
  rw [hA]
  native_decide

/- b) \(\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}\)-/
theorem number_theory_4733_2 {A : Matrix (Fin 2) (Fin 2) (ZMod 5)} (hA : A = !![1, 2; 3, 4]) :
    A * !![3, 1; 4, 2] = 1 := by
  -- verify by computation
  rw [hA]
  native_decide

/- c) \(\begin{pmatrix} 2 & 2 \\ 1 & 2 \end{pmatrix}\)-/
theorem number_theory_4733_3 {A : Matrix (Fin 2) (Fin 2) (ZMod 5)} (hA : A = !![2, 2; 1, 2]) :
    A * !![1, 4; 2, 1] = 1 := by
  -- verify by computation
  rw [hA]
  native_decide
