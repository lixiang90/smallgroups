# Export pc-presentation data for all small groups of order @N@ from GAP.
# Used by Scripts/translate_pc.py: replace @N@ with the order, feed to GAP on stdin.
#
# Output format (whitespace-separated, GAP list syntax `[ 2, 0, 1 ]`):
#   GROUP <N> <j>
#   RELORDERS [ r1, ..., rn ]
#   POWER i [ e1, ..., en ]      (exponents of g_i ^ r_i)
#   CONJ i k [ e1, ..., en ]     (exponents of g_k ^ (g_i^-1), k > i)
#   END
#
# NOTE: the tower convention of `CycExt` is `t * g * t^-1 = f(g)`, so the layer
# automorphism is conjugation by the *inverse* of the new generator; hence the
# export conjugates by `g_i^-1`.

ExportPC := function(N)
  local j, G, pcgs, ro, n, i, k;
  for j in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, j);
    pcgs := Pcgs(G);
    ro := RelativeOrders(pcgs);
    n := Length(pcgs);
    Print("GROUP ", N, " ", j, "\n");
    Print("RELORDERS ", ro, "\n");
    for i in [1..n] do
      Print("POWER ", i, " ", ExponentsOfPcElement(pcgs, pcgs[i]^ro[i]), "\n");
    od;
    for i in [1..n] do
      for k in [i+1..n] do
        Print("CONJ ", i, " ", k, " ",
          ExponentsOfPcElement(pcgs, pcgs[k]^(pcgs[i]^-1)), "\n");
      od;
    od;
    Print("END\n");
  od;
end;

ExportPC(@N@);
