/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasCompound

namespace CapacityAtlasCompound.AuditFixtures

/-- This valid theorem deliberately omits the canonical universe generality. -/
theorem universeZeroCertificate {X S Y : Type} [Fintype X] [Fintype S] [Fintype Y]
    [Nonempty X] [Nonempty S] (channels : S → CapacityAtlas.FiniteChannel X Y) :
    CapacityAtlas.Channel.compoundCapacityStatement channels :=
  CapacityAtlasCompound.capacityCertificate channels

end CapacityAtlasCompound.AuditFixtures
