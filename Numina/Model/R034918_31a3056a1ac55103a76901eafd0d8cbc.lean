import Mathlib

theorem algebra_98239 (a b c d e k : ℤ) (hb : b = a + k) (hc : c = b + k) (hd : d = c + k) (he : e = d + k) (h: a + b + c + d + e = 30) :
c = 6 := by
  have hb' : b = a + k := hb
  have hc' : c = a + 2 * k := by 
    linarith [hc, hb']
  have hd' : d = a + 3 * k := by 
    linarith [hd, hc']
  have he' : e = a + 4 * k := by 
    linarith [he, hd']
  have h1 : a + (a + k) + (a + 2 * k) + (a + 3 * k) + (a + 4 * k) = 30 := by 
    rw [hb', hc', hd', he'] at h
    linarith 
  have h2 : a + 2 * k = 6 := by 
    linarith 
  linarith [hc', h2]