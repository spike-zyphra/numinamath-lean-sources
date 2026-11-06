import Mathlib
set_option maxHeartbeats 0

/- Let $x, y, z$ be three distinct positive integers. Prove that

$$
(x+y+z)(x y+y z+z x-2) \geq 9 x y z
$$

When does the equality hold? -/
theorem inequalities_605808 (x y z : ℕ) (xpos : x > 0) (ypos : y > 0) (zpos : z > 0)
(xney : x ≠ y) (ynez : y ≠ z) (znex : z ≠ x) : (x + y + z) * (x * y + y * z + z * x - 2) ≥ 9 * x * y * z
∧ ((x + y + z) * (x * y + y * z + z * x - 2) = 9 * x * y * z ↔ ∃ k, ({x, y, z} : Set ℕ) = {k, k + 1, k + 2}) := by
-- Assume w. l. o. g. that $z< y$
  wlog zlty : z < y
  · replace zlty : y < z := by apply lt_of_le_of_ne; linarith; exact ynez
    specialize this x z y xpos zpos ypos (Ne.symm znex) (Ne.symm ynez) (Ne.symm xney) zlty
    ring_nf at *; constructor; exact this.left; rw [this.right, Set.insert_eq, Set.insert_eq]
    nth_rw 2 [Set.union_comm]; rw [← Set.insert_eq, ← Set.insert_eq]; ring_nf
-- Assume w. l. o. g. that $z< x$
  wlog zltx : z < x
  · replace zltx : x < z := by apply lt_of_le_of_ne; linarith; exact id (Ne.symm znex)
    specialize this z y x zpos ypos xpos (Ne.symm ynez) (Ne.symm xney) (Ne.symm znex) (show _ by linarith) zltx
    ring_nf at *; constructor; exact this.left; rw [this.right, Set.insert_eq, Set.insert_eq]
    rw [Set.union_comm]; nth_rw 2 [Set.union_comm]; rw [Set.union_assoc]
    rw [← Set.insert_eq, ← Set.insert_eq]; ring_nf
-- Assume w. l. o. g. that $y< x$
  wlog yltx : y < x
  · replace yltx : x < y := by apply lt_of_le_of_ne; linarith; exact xney
    specialize this y x z ypos xpos zpos (Ne.symm xney) (Ne.symm znex) (Ne.symm ynez)
    specialize this (show _ by linarith) (show _ by linarith) yltx
    ring_nf at *; constructor; exact this.left; rw [this.right, Set.insert_eq, Set.insert_eq]
    rw [← Set.union_assoc]; nth_rw 2 [Set.union_comm]; rw [Set.union_assoc]
    rw [← Set.insert_eq, ← Set.insert_eq]; ring_nf
-- If $z+2$ is less or equal to $y$, show that the strict inequality holds
  have aux : z + 2 ≤ y → 9 * x * y * z < (x + y + z) * (x * y + y * z + z * x - 2) := by
    intro h; let zltx' := zltx; let yltx' := yltx; let h' := h
    rw [Nat.lt_iff_add_one_le] at yltx'; replace zltx' : z + 3 ≤ x := by linarith
    rw [← Nat.le_sub_iff_add_le', ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)] at zltx' yltx' h'
    norm_num at zltx yltx h; simp [pow_two, Nat.mul_sub, Nat.sub_mul] at zltx' yltx' h'
    rw [Nat.le_sub_iff_add_le, ← Nat.add_sub_assoc, Nat.sub_le_iff_le_add', ← Nat.add_sub_assoc] at zltx' yltx' h'
    rw [Nat.le_sub_iff_add_le] at zltx' yltx' h'; ring_nf at zltx' yltx' h'; calc
      _ < 9 * x * y * z + (2 * x + 7 * y - z) := by rw [Nat.lt_add_right_iff_pos, Nat.sub_pos_iff_lt]; linarith
      _ ≤ (x + y + z) * (x * y + y * z + z * x - 2) := by
        rw [Nat.mul_sub, Nat.le_sub_iff_add_le, add_assoc, mul_two]
        nth_rw 2 [← add_assoc]; rw [← Nat.sub_add_comm]; nth_rw 3 [← add_assoc]
        rw [Nat.add_sub_cancel]; calc
          _ = x * y * z * 3 + ((1 + x * y * 2) * z + (4 + z * y * 2) * x + (9 + x * z * 2) * y) := by ring
          _ ≤ x * y * z * 3 + ((x ^ 2 + y ^ 2) * z + (z ^ 2 + y ^ 2) * x + (x ^ 2 + z ^ 2) * y) := by gcongr
          _ = _ := by ring
        linarith; rw [mul_le_mul_left]; rw [add_assoc]; apply Nat.le_add_right_of_le
        rw [show 2 = 2*1 by simp]; gcongr; all_goals linarith
    any_goals rw [add_comm]; apply Nat.le_add_right_of_le; rw [mul_le_mul_right]; any_goals linarith
    any_goals rw [mul_le_mul_right]; any_goals linarith
    any_goals simp [← Nat.sub_mul]; rw [mul_le_mul_left]; any_goals linarith
    any_goals rw [Nat.sub_pos_iff_lt]; any_goals linarith
    any_goals linarith
  constructor
  -- To prove the inequality, we first assume $z+2≤y$ then apply aux to finish this case
  · by_cases h : z + 2 ≤ y; specialize aux h; linarith
  -- Otherwise, we have $y=z+1$. We can use this to simplify the inequality and rearrange the terms, the goal will follow
    replace h : y = z + 1 := by linarith
    simp [h]; zify; rw [Nat.cast_sub]; push_cast; rw [← sub_nonneg]; calc
      _ ≤ ((x : ℤ) - z - 2) * (x - z + 1) * (2 * z + 1) := by
        apply mul_nonneg; apply mul_nonneg; rw [sub_sub, sub_nonneg]; linarith
        rw [sub_add_eq_add_sub, sub_nonneg]; linarith; positivity
      _ = _ := by ring
    rw [add_assoc]; apply Nat.le_add_right_of_le
    rw [show 2 = 2*1 by simp]; gcongr; all_goals linarith
  constructor
  -- To prove the condition when equality holds, we first rule out the case when $z+2≤y$ because of the lemma aux
  · intro h; by_cases h' : z + 2 ≤ y; specialize aux h'; linarith
  -- Otherwise, we have $y=z+1$. We can use this to simplify the equality and factorize it
    replace h' : y = z + 1 := by linarith
    rw [h'] at h; zify at h; rw [Nat.cast_sub, ← sub_eq_zero] at h; push_cast at h
    rw [show ((x:ℤ)+(z+1)+z)*(x*(z+1)+(z+1)*z+z*x-2)-9*x*(z+1)*z = ((x : ℤ) - z - 2) * (x - z + 1) * (2 * z + 1) by ring] at h
    rw [mul_assoc, mul_eq_zero_iff_right, sub_sub, sub_eq_zero] at h; norm_cast at h
  -- Prove that we can use $z$ to fulfill the final goal
    use z; rw [h, h', Set.insert_eq, Set.insert_eq, Set.union_comm]; nth_rw 2 [Set.union_comm]
    rw [Set.union_assoc, ← Set.insert_eq, ← Set.insert_eq]
    suffices : 0 < ((x:ℤ) - z + 1) * (2 * z + 1); linarith
    apply mul_pos; rw [sub_add_eq_add_sub, sub_pos]; linarith; positivity
    rw [add_assoc]; apply Nat.le_add_right_of_le
    rw [show 2 = 2*1 by simp]; gcongr; all_goals linarith
-- Conversely, if the condition holds, then we must have $z=k$, $y=k+1$ and $x=k+2$. It is straightforward to check the equation holds true.
  rintro ⟨k, hk⟩; simp [Set.ext_iff] at hk
  have h1 := hk k; have h2 := hk (k+1); have h3 := hk (k+2); simp at h1 h2 h3
  rcases h1 with h1|h1|h1 <;> rcases h2 with h2|h2|h2 <;> rcases h3 with h3|h3|h3; all_goals simp_all
  any_goals linarith
  zify; rw [Nat.cast_sub, ← h2, ← h3]; push_cast; ring
  rw [add_assoc]; apply Nat.le_add_right_of_le
  rw [show 2 = 2*1 by simp]; gcongr; all_goals linarith
