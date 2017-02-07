// Implementation of computing neighbor lattices.

import "helper.m" : MVM;
    
function LiftSubspace(nProc : BeCareful := true, Override := false)
	// If we try to lift an empty subspace, return trivial entries.
	if nProc`isoSubspace eq [] then return [], [], []; end if;

	// The local data.
	Vpp := nProc`L`Vpp[nProc`pR];

	// The characteristic of the finite field.
	ch := Vpp`ch;

	// The standarized basis.
	basis := Vpp`V`Basis;

	// The requested isotropic dimension.
	k := nProc`k;

	// The pR-isotropic subspace.
	sp := nProc`isoSubspace;

	// The dimension.
	dim := Dimension(nProc`L);

	// The hyperbolic dimension.
	hDim := 2 * Vpp`V`WittIndex;

	// The affine vector space.
	V := Vpp`V;

	// Shortcuts to the projection maps.
	map := Vpp`proj_pR;
	proj := Vpp`proj_pR2;

	if not Override then
		// Retrieve parameterization data regarding the affine space.
		param := V`ParamArray[k];

		// Get the pivots for the bases of the isotropic subspaces.
		pivots := param`Pivots[param`PivotPtr];
	else
		pivots := [0^^k];
		for i in [1..k] do
			pos := 0;
			repeat pos +:= 1;
			until sp[i][pos] ne 0;
			pivots[i] := pos;
		end for;
	end if;

	// Set up the correct basis vectors.
	for i in [1..k], j in [pivots[i]+1..dim] do
		AddColumn(~basis, sp[i][j], j, pivots[i]);
	end for;

	// Extract our target isotropic subspace modulo pR.
	X := [ MVM(basis, V.i) : i in pivots ];

	// Extract the hyperbolic complement modulo pR.
	paired := [ hDim+1-pivots[k+1-i] : i in [1..k] ];
	Z := [ MVM(basis, V.i) : i in paired ];

	// Extract the remaining basis vectors.
	exclude := pivots cat paired;
	U := [ MVM(basis, V.i) : i in [1..dim] | not i in exclude ];

	// Convert to coordinates modulo pR^2.
	X := [ Vector([ proj(e @@ map) : e in Eltseq(x) ]) : x in X ];
	Z := [ Vector([ proj(e @@ map) : e in Eltseq(z) ]) : z in Z ];
	U := [ Vector([ proj(e @@ map) : e in Eltseq(u) ]) : u in U ];

	// Build the coordinate matrix.
	B := Matrix(X cat Z cat U);

	function __gram(B : quot := true)
		// In odd characteristic, things are exactly as we expect.
		if ch ne 2 then
			return B * Vpp`quotGram * Transpose(B);
		end if;

		// Promote the basis to the number ring.
		B := ChangeRing(B, Integers());

		gram := ChangeRing(GramMatrix(nProc`L), Integers());

		// Compute the Gram matrix.
		gram := B * gram * Transpose(B);

		// The dimension.
		dim := Nrows(B);

		// Return the appropriate Gram matrix.
		if quot then
			return Matrix(Vpp`quot, dim, dim, Eltseq(gram));
		else
			return gram;
		end if;
	end function;

	// Compute the Gram matrix of the subspace with respect to the spaces
	//  we will perform the following computations upon.
	gram := __gram(Matrix(X cat Z));

	// Lift Z so that it is in a hyperbolic pair with X modulo pR^2.
	Z := [ Z[i] +
		&+[ ((i eq j select 1 else 0) - gram[k+1-j,i+k]) * Z[j]
			: j in [1..k] ] : i in [1..k] ];

	// Verify that X and Z form a hyperbolic pair.
	if BeCareful then
		// Compute the Gram matrix thusfar.
		B := Matrix(X cat Z cat U);
		temp := __gram(B);

		// Verify that we have ones and zeros in all the right places.
		assert &and[ temp[i,k+j] eq (i-k+j eq 1 select 1 else 0)
			: i,j in [1..k] ];
	end if;

	// We will need to divide by 2, so we will need to consider the Gram
	//  matrix over the base ring instead of over the ring modulo pR^2.
	if ch eq 2 then
		gram := __gram(Matrix(X cat Z) : quot := false);
	end if;

	// Lift X so that it is isotropic modulo pR^2.
	X := [ X[i] +
		&+[ -(gram[i,k+1-j]) / (i+j-1 eq k select 2 else 1) * Z[j]
			: j in [k+1-i..k] ] : i in [1..k] ];

	// Verify that X is isotropic modulo pR^2.
	if BeCareful then
		// The basis.
		B := Matrix(X);

		// The Gram matrix on this basis.
		temp := __gram(B);

		// Verify all is well.
		assert &and[ temp[i,j] eq 0 : i,j in [1..k] ];
	end if;

	// Lift Z so that it is isotropic modulo pR^2.
	Z := [ Z[i] -
		&+[ gram[k+i,2*k+1-j] / (i+j-1 eq k select 2 else 1) * X[j]
			: j in [k+1-i..k] ] : i in [1..k] ];

	// Verify that Z is isotropic modulo pR^2.
	if BeCareful then
		// The basis.
		B := Matrix(Z);

		// The Gram matrix on this basis.
		temp := __gram(B);

		// Verify all is well.
		assert &and[ temp[i,j] eq 0 : i,j in [1..k] ];
	end if;

	// The Gram matrix thusfar.
	gram := __gram(Matrix(X cat Z cat U));

	// Make U orthogonal to X+Z.
	for i in [1..k], j in [1..dim-2*k] do
		// Clear components corresponding to X.
		scalar := gram[2*k+1-i,2*k+j];
		U[j] -:= scalar * X[i];

		// Clear components corresponding to Z.
		scalar := gram[k+1-i,2*k+j];
		U[j] -:= scalar * Z[i];
	end for;

	// Verify that U is now orthogonal to X+Z.
	if BeCareful then
		// The basis.
		B := Matrix(X cat Z cat U);

		// The Gram matrix.
		temp := __gram(B);

		// Verify correctness.
		assert &and[ temp[i,j] eq 0
			: i in [1..2*k], j in [2*k+1..dim] ];
	end if;

	return X, Z, U;
end function;

intrinsic BuildNeighborProc(L, pR, k : BeCareful := true) -> NeighborProc
    {-Create neigbor iteration -}
	// Initialize the neighbor procedure.
	nProc := New(NeighborProc);

	// Assign the lattice, prime ideal, and isotropic dimension.
	nProc`L := L;
	nProc`pR := pR;
	nProc`k := k;

	// The dimension.
	dim := Dimension(L);

	// If an associative array hasn't been assigned, assign one.
	if not assigned L`Vpp then L`Vpp := AssociativeArray(); end if;

	if not IsDefined(L`Vpp, pR) then
		// Initialize the affine quadratic space.
		qAff := New(QuadSpaceAff);

		// The prime ideal.
		qAff`pR := pR;

		// A uniformizing element of pR.
		qAff`pElt := pR;

		// The residue class field.
		qAff`F, qAff`proj_pR := ResidueClassField(pR);

		// Assign the characteristic.
		qAff`ch := Characteristic(qAff`F);

		// The quotient modulo p^2.
		qAff`quot, qAff`proj_pR2 := quo< Integers() | pR^2 >;

		// The gram matrix.
		gram := GramMatrix(L);

		// This Gram matrix modulo p.
		mat := qAff`proj_pR(gram);

		// The Gram matrix modulo p^2.
		qAff`quotGram := Matrix(qAff`quot, dim, dim,
			[ qAff`proj_pR2(e) : e in Eltseq(gram) ]);

		// Make some adjustments when we're in characteristic 2.
		if qAff`ch eq 2 then
			// Adjust the diagonal entries accordingly.
			for i in [1..dim] do
				value := gram[i,i] / 2;
				mat[i,i] := qAff`proj_pR(value);
				qAff`quotGram[i,i] := qAff`proj_pR2(value);
			end for;
		end if;

		// The affine quadratic space.
		qAff`V := BuildQuadraticSpace(mat);

		// Add this space to our associative array.
		L`Vpp[pR] := qAff;
	end if;

	// Retrive the affine quadratic space we're interested in.
	Vpp := L`Vpp[pR];

	// Make sure that the Witt index is not too large.
	// TODO: Fix this so that it returns an empty list instead of killing
	//  the program, since we will want to allow for the computation of
	//  zero Hecke matrices at primes for which exceed the Witt index.
	//assert Vpp`V`WittIndex ge k;

	// Build the skew vector.
	nProc`skewDim := Integers()!(k*(k-1)/2);
	if nProc`skewDim ne 0 then
		nProc`skew := Zero(MatrixRing(Vpp`F, k));
	end if;

	// Retrieve the first isotropic subspace of the given dimension.
	nProc`isoSubspace := FirstIsotropicSubspace(Vpp`V, k);

	// Lift subspace so that X and Z are a hyperbolic pair modulo p^2 and
	//  U is the hyperbolic complement to X+Z modulo p^2.
	nProc`X, nProc`Z, nProc`U :=
		LiftSubspace(nProc : BeCareful := BeCareful);
	nProc`X_skew := [ x : x in nProc`X ];

	return nProc;
end intrinsic;

intrinsic BuildNeighbor(nProc : BeCareful := true, UseLLL := true,
    Special := false) -> Lat
    {-Retrive current iterate-}
	// Shortcut for the projection map modulo pR^2.
	proj := nProc`L`Vpp[nProc`pR]`proj_pR2;

	// The diension.
	dim := Dimension(nProc`L);

	// Pull the pR^2-isotropic basis back to the number ring.
	XX := [ Vector([ e @@ proj : e in Eltseq(x) ]) : x in nProc`X_skew ];
	ZZ := [ Vector([ e @@ proj : e in Eltseq(z) ]) : z in nProc`Z ];
	UU := [ Vector([ e @@ proj : e in Eltseq(u) ]) : u in nProc`U ];
	BB := Rows(Id(MatrixRing(Integers(), dim)));

	// The vectors we'll perform HNF on; they need to be scaled by p so
	//  that HNF will be happy. We'll undo this once we perform HNF.
	ZZ := [ nProc`pR^2 * v : v in ZZ ];
	UU := [ nProc`pR * v : v in UU ];
	BB := [ nProc`pR^3 * v : v in BB ];

	// Perform HNF.
	H := HermiteForm(Matrix(XX cat ZZ cat UU cat BB));
	H := Rows(H);

	// Get new basis for the neighbor lattice.
	nLatBasis := Matrix([ ChangeRing(H[i], Rationals()) / nProc`pR
		: i in [1..dim] ]);

	// The new basis for the neighbor lattice with respect to the standard
	//  coordinates.
	newBasis := nLatBasis * Matrix(Basis(nProc`L));

	// The inner form.
	innerForm := ChangeRing(InnerProductMatrix(nProc`L), Rationals());

	// Rebuild the neighbor lattice in standard coordinates.
	nLat := LatticeWithBasis(newBasis, innerForm);

	if BeCareful then
		// Compute the intersection lattice.
		intLat := nLat meet nProc`L;

		// Verify that this neighbor has the proper index properties.
		assert Index(nProc`L, intLat) eq nProc`pR^nProc`k;
		assert Index(nLat, intLat) eq nProc`pR^nProc`k;
		assert IsIntegral(nLat);
	end if;
	return nLat;
end intrinsic;

intrinsic GetNextNeighbor(nProc : BeCareful := true) -> NeighborProc
    {-Advance cursor-}
	// The affine data.
	Vpp := nProc`L`Vpp[nProc`pR];

	// The isotropic dimension we're interested in.
	k := nProc`k;

	// The starting position of the skew vector to update.
	row := 1; col := 1;

	// A nonzero element modulo pR^2 which is 0 modulo pR.
	pElt := Vpp`proj_pR2(Vpp`pElt);

	// Update the skew matrix (only for k ge 2).
	if nProc`skewDim ne 0 then
		repeat
			// Flag for determining whether we are done updating
			//  the skew matrix.
			done := true;

			// Increment valud of the (row,col) position.
			nProc`skew[row,col] +:= 1;

			// Update the coefficient of the skew matrix reflected
			//  across the anti-diagonal.
			nProc`skew[k-col+1,k-row+1] := -nProc`skew[row,col];

			// If we've rolled over, move on to the next position.
			if nProc`skew[row,col] eq 0 then
				// The next column of our skew matrix.
				col +:= 1;

				// Are we at the end of the column?
				if row+col eq k+1 then
					// Yes. Move to the next row.
					row +:= 1;

					// And reset the column.
					col := 1;
				end if;

				// Indicate we should repeat another iteration.
				done := false;
			end if;
		until done or row+col eq k+1;
	end if;

	// If we haven't rolled over, update the skew space and return...
	if row+col lt k+1 then
		// Shortcuts for the projection maps modulo pR and pR^2.
		map := Vpp`proj_pR;
		proj := Vpp`proj_pR2;

		// Update the skew space.
		nProc`X_skew := [ nProc`X[i] + pElt *
			&+[ proj(nProc`skew[i,j] @@ map) * nProc`Z[j]
				: j in [1..k] ] : i in [1..k] ];

		return nProc;
	end if;

	// ...otherwise, get the next isotropic subspace modulo pR.
	nProc`isoSubspace := NextIsotropicSubspace(Vpp`V, k);

	// Lift the subspace if we haven't reached the end of the list.
	if nProc`isoSubspace ne [] then
		nProc`X, nProc`Z, nProc`U :=
			LiftSubspace(nProc : BeCareful := BeCareful);
		nProc`X_skew := [ x : x in nProc`X ];
	end if;
	return nProc;
end intrinsic;

function SkipToNeighbor(nProc, space : BeCareful := true)
	nProc`isoSubspace := [ space ];
	nProc`X, nProc`Z, nProc`U := LiftSubspace(nProc
		: BeCareful := BeCareful, Override := true);
	nProc`X_skew := [ x : x in nProc`X ];
	return nProc;
end function;

