import Mathlib

lemma aux_4616 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hxy : x ≤ y) :
    (Nat.factorial x + Nat.factorial y = Nat.factorial z) ↔ (x = 1 ∧ y = 1 ∧ z = 2) := by
  constructor
  -- prove x!+y!=z! has only 2 solutions
  intro h
  generalize eq:y-x=a
  have hya:y=x+a:= by rw[←eq,←Nat.add_sub_assoc,add_comm ];simp;exact hxy
  rw[hya] at h
  -- let y=x+a
  have hzxa:z>x+a:= by
                      by_contra hz
                      simp at hz
                      have hzf:= Nat.factorial_le hz
                      rw[←h] at hzf
                      have :x.factorial≤0:= by linarith
                      have :=Nat.factorial_pos x
                      linarith
  generalize eq2:z-(x+a)=b
  -- let z=x+a+b
  have hzab:z=x+a+b:= by rw [←eq2,←Nat.add_sub_assoc,add_comm ];simp;linarith
  rw [hzab] at h
  have hb:b>0:=by linarith
  -- prove x!+(x+a)!=(x+a+b)! ↔  x!(1+(x+a).ascFactorial b)=x!*(x+a+b).ascFactorial b
  rw[ ← Nat.factorial_mul_ascFactorial] at h
  rw[ ← Nat.factorial_mul_ascFactorial] at h
  rw[ ← Nat.factorial_mul_ascFactorial] at h
  have hxf:x.factorial + x.factorial * (x + 1).ascFactorial a = x.factorial * (1+(x + 1).ascFactorial a):= by linarith
  conv at h=>lhs;rw[hxf]
  rw [mul_assoc] at h
  have h:= Nat.mul_left_cancel (Nat.factorial_pos x) h
  have hasc:2 ≤ (x + a + 1).ascFactorial b := by
    apply ge_trans (Nat.pow_succ_le_ascFactorial _ _)
    rw[ge_iff_le]
    have hmin:= @Nat.pow_le_pow_right (x+a+1) (by linarith) 1 b (by linarith)
    apply ge_trans hmin
    linarith
  -- consider x=1
  by_cases hx:x=1
  rw[hx] at hasc
  -- consider a=1
  by_cases ha:a=0
  rw[ha,hx] at h
  simp at h
  -- consider b=1
  by_cases hb1:b=1
  constructor
  exact hx
  constructor
  rw[hya,hx,ha]
  rw[hzab,hx,ha,hb1]
  -- find contradiction
  have hb2:2≤b:= by omega
  have hb22:=(Nat.pow_succ_le_ascFactorial 2 b)
  rw[← h] at hb22
  apply False.elim
  -- repeatly use (x+a).ascFactorial b >= (x+a)^b >= (x+a)^constant, when b>= constant
  have hmin:= @Nat.pow_le_pow_right 2 (by linarith) 2 b (by linarith)
  linarith
  rw[hx] at h
  simp at h
  have ha: 1≤a:= by omega
  have ha22:=(Nat.pow_succ_le_ascFactorial 2 a)
  have hmin:= @Nat.pow_le_pow_right 2 (by linarith) 1 a (by linarith)
  have h1:1 + Nat.ascFactorial 2 a < 2*Nat.ascFactorial 2 a:= by linarith
  rw [h] at h1
  have :Nat.ascFactorial 2 a * 2 ≤ Nat.ascFactorial 2 a * (1 + a + 1).ascFactorial b:= by apply mul_le_mul; rfl;exact hasc;norm_num;linarith
  have :Nat.ascFactorial 2 a * 2 < 2*Nat.ascFactorial 2 a := by linarith
  apply False.elim
  linarith
  have hx:2≤x:= by omega
  have :(x + 1).ascFactorial a * 2 ≤ (x + 1).ascFactorial a * (x + a + 1).ascFactorial b:= by apply mul_le_mul; rfl;exact hasc;norm_num;linarith
  rw [←h] at this
  have hb22:=(Nat.pow_succ_le_ascFactorial (x+1) a)
  apply False.elim
  by_cases ha:a=0
  rw[ha] at h
  simp at h
  have hb22:=(Nat.pow_succ_le_ascFactorial (x+1) b)
  rw [← h] at hb22
  have hmin:= @Nat.pow_le_pow_right (x+1) (by linarith) 1 b (by linarith)
  linarith
  have ha:1≤a:= by omega
  have hmin:= @Nat.pow_le_pow_right (x+1) (by linarith) 1 a (by linarith)
  linarith
  -- prove the other side
  intro h
  rw[h.1,h.2.1,h.2.2]
  simp

theorem number_theory_4616 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
    (Nat.factorial x + Nat.factorial y = Nat.factorial z)↔ (x = 1 ∧ y = 1 ∧ z = 2):= by
  by_cases hxy: x ≤ y
  -- if x ≤ y, then direct use the lemma
  have := aux_4616 x y z hx hy hz hxy
  tauto
  push_neg at hxy
  have hxy:y ≤ x := by linarith
  have h1 := aux_4616 y x z hy hx hz hxy
  -- swap x,y
  constructor
  · -- prove if Nat.factorial x + Nat.factorial y = Nat.factorial z then (x=1∧y=1∧z=2)
    intro h
    have h2: Nat.factorial y + Nat.factorial x = Nat.factorial z := by linarith
    have h3 := h1.mp h2
    -- swap x,y in solution
    aesop
    all_goals try {tauto}
    all_goals
      try { norm_num at * }
    <;> try tauto
    <;> try { 
      omega <;> try { norm_num }
    }
  · -- prove if (x=1∧y=1∧z=2) then Nat.factorial x + Nat.factorial y = Nat.factorial z
    rintro ⟨rfl, rfl, rfl⟩
    simp
    all_goals
      try { norm_num }
    <;> try { tauto }
    <;> try omega
    <;> try norm_num at *
    <;> try tauto
    all_goals
      try { 
        tauto <;> try norm_num
      }
      <;> try omega
    <;> try { 
      tauto <;> try norm_num
    }
    <;> try omega