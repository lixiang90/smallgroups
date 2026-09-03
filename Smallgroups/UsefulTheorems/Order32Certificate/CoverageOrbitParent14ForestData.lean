/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core

namespace Smallgroups.UsefulTheorems.Order32Certificate

/-- Row-major indexing of independently checked forest chunks. -/
def orbitP14ForestChunkIndex (c : Fin 16)
    (j : Fin 64) : Fin 1024 :=
  ⟨c.val * 64 + j.val, by omega⟩

end Smallgroups.UsefulTheorems.Order32Certificate
