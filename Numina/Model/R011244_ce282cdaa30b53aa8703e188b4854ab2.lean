import Mathlib
import Aesop

theorem AIME_Algebra_724 (fstqt sndqt trdqt: ℚ) (hfst:fstqt=1/4) (hsnd:sndqt=(1000/4)/(900))(htrd:trdqt=((1000/4)/(800)))(m:ℕ):(fstqt+sndqt+trdqt+(1000/4)/((800+m))≤1)↔766≤m:= by
  constructor
  · -- Forward direction: inequality implies 766 ≤ m
    intro h
    rw [hfst, hsnd, htrd] at h
    -- Expand the hypothesis to its components.
    -- Use `interval_cases` to examine all cases from 0 to 765.
    by_contra h1
    push_neg at h1
    have h2 : m < 766 := h1
    have : m ≤ 765 := by omega
    interval_cases m <;> norm_num at h <;> try { tauto } <;> try { linarith } <;> try { tauto }
  · -- Backward direction: 766 ≤ m implies inequality
    intro h
    rw [hfst, hsnd, htrd]
    have h1 : (m : ℚ) ≥ (766 : ℚ) := by exact_mod_cast h
    have h2 : (800 + (m : ℚ)) ≥ (1566 : ℚ) := by
      nlinarith
    have h3 : (1000 / 4 : ℚ) / ((800 + (m : ℚ))) ≤ (1000 / 4 : ℚ) / (1566 : ℚ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    norm_num at h3 ⊢
    all_goals
      try { 
        nlinarith [h3, show (m : ℚ) ≥ (0 : ℚ) by positivity]
      }
      <;> try { tauto } <;> try { 
        linarith [h3, show (m : ℚ) ≥ (0 : ℚ) by positivity]
      }
      <;> try { tauto }
      <;> try { 
        interval_cases m <;> norm_num at h3 ⊢ <;> try { tauto }
        <;> try { nlinarith }
        <;> try { tauto }
      }
      <;> done