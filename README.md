# Capacity Atlas: finite compound channels

A Lean proof of the max–min capacity formula for a known finite nonempty family of finite discrete memoryless channels. A fixed unknown member governs the whole block. Neither terminal knows that member; one deterministic encoder and one deterministic decoder must work for every member, without feedback or input constraints.

Messages are uniform. Average error vanishes uniformly over the family, with codes at every sufficiently large blocklength. Rates and capacity are measured in bits per channel use.

The direct proof applies threshold random coding to a uniform mixture of entire block channels and bounds each member's error using the mixture error. The converse retains the same averaged input distribution for every channel before taking the minimum, using entropy subadditivity, mutual-information concavity, and Fano's inequality. Compactness of the finite input simplex supplies a maximizing distribution.

The Atlas model and reusable APIs are pinned in `lakefile.toml`. `CapacityAtlasCompound.capacityCertificate` proves `CapacityAtlas.Channel.compoundCapacityStatement` directly. The audit checks all transitive proof axioms and compares the certificate type against the canonical proposition with every parameter. Negative controls reject a different proposition and a certificate restricted to smaller universes.

Run `lake --wfail build` and `lake exe capacity_compound_audit`.

Primary sources: Blackwell, Breiman, and Thomasian, [The Capacity of a Class of Channels](https://doi.org/10.1214/aoms/1177706106), Annals of Mathematical Statistics 30(4), 1229–1241 (1959); Lapidoth and Telatar, [The Compound Channel Capacity of a Class of Finite-State Channels](https://infoscience.epfl.ch/server/api/core/bitstreams/86a85253-ceb6-45ea-970f-ab907c765f69/content), IEEE Transactions on Information Theory 44(3), 973–983 (1998). The latter's equation (1), page 973 model discussion, and Definition 1 were visually checked against the original PDF. Its natural-log normalization is converted to bits here.

AI assistance was used for research, implementation, and review. Human review of statement faithfulness and literature attribution is required before merge.

License: Apache-2.0.
