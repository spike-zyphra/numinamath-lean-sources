import Mathlib

open Real

theorem algebra_157018 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, 0 < x → 0 < y → f x y = x * y / (x + y)) :
    (∀ x y, 0 < x → 0 < y → f x y = f y x) ∧ (∀ x y z, 0 < x → 0 < y → 0 < z → f x (f y z) = f (f x y) z) := by
  constructor
  · -- Show commutative.
    intros x y hx hy
    have h1 : f x y = x * y / (x + y) := hf x y hx hy
    have h2 : f y x = y * x / (y + x) := hf y x hy hx
    rw [h1, h2]
    have h3 : x * y = y * x := by ring
    have h4 : x + y = y + x := by ring
    rw [h3, h4]
    all_goals
      linarith
      all_goals
        positivity
  · -- Show that $f$ is associative 
    intros x y z hx hy hz
    have eq1 : f y z = y * z / (y + z) := hf y z hy hz
    have eq2 : f x y = x * y / (x + y) := hf x y hx hy
    have eq3 : f x (f y z) = (x * (y * z / (y + z))) / (x + (y * z / (y + z))) := by
      rw [eq1]
      all_goals 
      try { 
        apply hf 
        all_goals 
        try { positivity } 
        all_goals 
        try { linarith [hx, hy, hz] } 
      }
      all_goals
      try { linarith [hx, hy, hz] }
    have eq5 : f (f x y) z = ((x * y / (x + y)) * z) / ((x * y / (x + y)) + z) := by 
      rw [eq2]
      all_goals 
      try { 
        apply hf 
        all_goals 
        try { positivity } 
        all_goals 
        try { linarith [hx, hy, hz] } 
      }
      all_goals
      try { linarith [hx, hy, hz] }
    rw [eq3, eq5]
    have pos1 : 0 < y + z := by linarith
    have pos2 : 0 < x + y := by linarith
    have hpos3 : 0 < x + (y * z / (y + z)) := by
      have hx_pos : 0 < x := hx
      have hfrac_pos : 0 < y * z / (y + z) := by 
        apply div_pos
        · -- Show 0 < y * z
          nlinarith [show 0 < y from by linarith, show 0 < z from by linarith]
        · -- Show 0 < y + z
          linarith
      linarith
    have hpos4 : 0 < (x * y / (x + y)) + z := by 
      have hfrac_pos : 0 < x * y / (x + y) := by
        apply div_pos
        · -- Show 0 < x * y
          nlinarith [show 0 < x from by linarith, show 0 < y from by linarith]
        · -- Show 0 < x + y
          linarith
      have hz_pos : 0 < z := hz
      linarith
    field_simp [show 0 < y + z by linarith, show 0 < x + y by linarith, hpos3, hpos4]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
    <;> field_simp
    all_goals
      try { positivity }
      all_goals
        try { linarith }
        all_goals
          try { positivity }
          all_goals
            nlinarith