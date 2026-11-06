import Mathlib

/-
A sequence $s_{0}, s_{1}, s_{2}, s_{3}, \ldots$ is defined by $s_{0}=s_{1}=1$ and, for every positive integer $n, s_{2 n}=s_{n}, s_{4 n+1}=s_{2 n+1}, s_{4 n-1}=s_{2 n-1}+s_{2 n-1}^{2} / s_{n-1}$. What is the value of $s_{1000}$ ?
-/

theorem Number_theory_611037  (s : ℕ → ℝ) (hs0 : s 0 = 1) (hs1 : s 1 = 1) (h2n: ∀ n, s (2*n) = (s n)) (h4np1: ∀ n, s (4*n+1) = s (2*n+1) ) (h4nm1: ∀ n, s (4*n-1) = s (2*n-1) + (s (2*n-1))^2/ (s (n-1)) ) : s 1000 = 720 := by

-- just calculate it line by line using all the given relations.
  have s3: s 3 = 2 := by 
    have : s (4*1-1) = s (2*1-1) + (s (2*1-1))^2/ (s (1-1)) := by rw[h4nm1 1]
    ring_nf at this
    simp [this, hs0, hs1]; norm_num
  
  have s7:  s 7 = 6:= by 
    have : s (4*2-1) = s (2*2-1) + ((s (2*2-1))^2/(s (2*1-1))) := by rw[h4nm1 2];
    ring_nf at this
    field_simp [this, s3, hs1]; norm_num

  have s15: s 15 = 24 := by 
    have : s (4*4-1) = s (2*4-1) + (s (2*4-1))^2/ (s (4-1)) := by rw[h4nm1 4];
    ring_nf at this; 
    simp [this, s7, s3]; norm_num
  have s31: s 31 = 120 := by 
    have : s (4*8-1) = s (2*8-1) + (s (2*8-1))^2/ (s (8-1)) := by rw[h4nm1 8];
    ring_nf at this; 
    simp [this, s15, s7]; norm_num
  have s63: s 63 = 720 := by 
    have : s (4*16-1) = s (2*16-1) + (s (2*16-1))^2/ (s (16-1)) := by rw[h4nm1 16];
    ring_nf at this; 
    simp [this, s31, s15]; norm_num
  have s125: s 125 = 720 := by 
    have : s (4*31 +1) = s (2*31+1)   := by rw[h4np1 31];
    ring_nf at this
    simp [this, s63, s31]
  have : s 250 = 720 := by 
    calc
      s 250 = s (125 * 2) := by ring
      _ = s 125 := by rw[h2n 125]
      _ = 720 := by rw[s125]
  have : s 500 = 720 := by 
    calc
      s 500 = s (250 * 2) := by ring
      _ = s 250 := by rw[h2n 250]
      _ = 720 := by assumption
  
  have : s (2*500) = s 500 := by rw [h2n 500]
  have : 1000  = 2*500 := by norm_num
  rw [this]; linarith