import data.real.basic

example (a b c  : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  -- exact mul_mono_nonneg hc hab,
  rw ← sub_nonneg,
  have h_fact : b*c - a*c = (b - a)*c,
  { ring },
  rw h_fact,
  apply mul_nonneg, 
  { rw sub_nonneg,
    exact hab },
  { exact hc },
end

