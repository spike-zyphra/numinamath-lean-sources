import Mathlib

/- How many different combinations of 4 marbles can be made from 5 indistinguishable red marbles,
4 indistinguishable blue marbles, and 2 indistinguishable black marbles? -/

theorem combinatorics_610917 :
    ((Finset.range 6 ×ˢ Finset.range 5 ×ˢ Finset.range 3).filter (fun (x, y, z) => x + y + z = 4)).card = 12 := by

      native_decide