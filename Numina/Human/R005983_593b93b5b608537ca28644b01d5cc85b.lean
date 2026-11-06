import Mathlib

open Finset

/-Given a 9×9 chess board, we consider all the rectangles whose edges lie along grid lines
(the board consists of 81 unit squares, and the grid lines lie on the borders of the unit squares).
For each such rectangle, we put a mark in every one of the unit squares inside it. When this process is completed,
how many unit squares will contain an even number of marks?-/

theorem combinatorics_610967:
  ((Icc 1 9 ×ˢ Icc 1 9).filter (fun (i, j) => Even (i * (10 - i) * j * (10 - j)))).card = 56 := by

  native_decide