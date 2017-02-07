// The goal of this script is to convert a quadratic form defined over a finite
//  field into a standard form. This means that the quadratic form will be
//  expressed as hyperbolic + anisotropic + radical where the hyperbolic
//  component is antidiagonal. For example, we may have x1*x4 + x2*x3 + x5^2.

function MVM(M, v)
	return Vector(Transpose(M * Transpose(Matrix(v))));
end function;

function VerifyMatrix(M)
	// Get the base ring and its characteristic.
	F := BaseRing(M);
	char := Characteristic(F);

	// Ensure that the matrix is square.
	assert Nrows(M) eq Ncols(M);

	// The dimension.
	dim := Nrows(M);

	// Make sure the matrix is symmetric.
	assert IsSymmetric(M);

	// Create a vector space we'll be working over.
	V := VectorSpace(F, dim);

	return F, V, char, dim;
end function;

function FindIsotropicVector(M : Deterministic := true)
	// Get some useful information about the form / do a sanity check.
	F, V, char, dim := VerifyMatrix(M);

	if char ne 2 and Determinant(M) eq 0 then
		// Return the first vector in the null space.
		return true, Rows(NullspaceMatrix(M))[1];
	elif dim eq 1 then
		// Return the first basis vector.
		if M[1,1] eq 0 then return true, V.1; end if;
	elif dim eq 2 and char ne 2 then
		// Take care of the easy case first.
		if M[1,1] eq 0 then return true, V.1; end if;

		// Simplify things by giving the coefficients names.
		a := M[1,1]; b := M[1,2]; c := M[2,2];

		// The form is isotropic if and only if b^2-ac is a square.
		square, d := IsSquare(b^2-a*c);

		// If not a square, this form is anisotropic.
		if not square then return false, _; end if;

		// Since a ne 0 and the form is isotropic, we're done.
		return true, V.2 - ((b+d)/a) * V.1;
	elif dim eq 2 and char eq 2 then
		// Take care of the easy cases first.
		if M[1,1] eq 0 then return true, V.1; end if;
		if M[2,2] eq 0 then return true, V.2; end if;

		// Simplify things by giving the coefficients names.
		a := M[1,1]; b := M[1,2]; c := M[2,2];

		// If the off-diagonal term is zero, we can easily compute an
		//  isotropic vector.
		if b eq 0 then
			_, d := IsSquare(a / c);
			return true, V.1 + d * V.2;
		end if;

		// The form is isotropic if and only if the Artin-Schreier
		//  polynomial X^2+X+(ac/b^2) is reducible.
		R<X> := PolynomialRing(F);
		f := X^2 + X + a*c/b^2;

		// If the polynomial is irreducible, then there are no isotropic
		//  vectors to be found.
		if IsIrreducible(f) then return false, _; end if;

		// Otherwise, let's return an istropic vector.
		d := Roots(f)[1][1];
		return true, (d*b/a) * V.1 + V.2;
	else
		// Check the diagonal for an isotropic basis vector.
		for i in [1..dim] do
			if M[i,i] eq 0 then return true, V.i; end if;
		end for;

		if char eq 2 then
			// If we can find a pair of orthogonal basis vectors,
			//  we can easily construct an isotropic vector.
			for i in [1..dim-1], j in [i+1..dim] do
				if M[i,j] eq 0 then
					_, d := IsSquare(M[j,j] / M[i,i]);
					return true, d * V.i + V.j;
				end if;
			end for;

			// Otherwise, while the formulation is a bit more
			//  complicated, we can produce an isotropic vector
			//  by taking a linear combination of the first three
			//  basis vectors as follows:

			// Convenient references.
			a := M[1,1]; b := M[2,2]; c := M[3,3];
			d := M[2,3]; e := M[1,3]; f := M[1,2];

			// Find the square root of this complicated coefficient.
			_, g := IsSquare((b*e^2/f^2 + c + e*d/f)/a);

			// Return the isotropic vector.
			return true, g * V.1 + (e/f) * V.2 + V.3;
		end if;

		// In odd characteristic, start by considering only the first
		//  three variables.
		subM := Submatrix(M, 1, 1, 3, 3);

		// Save a copy of the submatrix so we can verify correctness.
		backupM := subM;

		// Change of basis matrix which realizes the isometry on this
		//  submatrix.
		basis := Id(GL(VectorSpace(F, 3)));

		// Clear the off-diagonal entries.
		for i in [1..2], j in [i+1..3] do
			scalar := -subM[i,j] / subM[i,i];
			AddColumn(~subM, scalar, i, j);
			AddRow(~subM, scalar, i, j);
			AddRow(~basis, scalar, i, j);

			// We may have inadvertantly created an isotropic basis
			//  vector, so let's make sure before we proceed.
			if subM[j,j] eq 0 then
				return true, Vector(Eltseq(basis[j]) cat
					 [ 0 : i in [4..dim] ]);
			end if;
		end for;

		// Make sure we didn't make a mistake.
		assert basis * backupM * Transpose(basis) eq subM;

		// Check if the first two variables alone are isotropic.
		square, d := IsSquare(-subM[1,1] * subM[2,2]);

		// If they are already isotropic, we're done.
		if square then
			vec := basis[1] + (M[1,1]/d) * basis[2];
			vec := Vector(Eltseq(vec) cat [ 0 : i in [4..dim] ]);
			return true, vec;
		end if;

		// The quadratic form over three variables.
		Q := QuadraticForm(subM);

		// Deterministically find an isotropic vector.
		if Deterministic then
			for x in F, y in F do
				// The quadratic form restricted to the first
				//  three variables.
				if Evaluate(Q, [x,y,1]) eq 0 then
					// Found an isotropic vector, return it.
					vec := x * basis[1] + y * basis[2] +
						basis[3];
					vec := Vector(Eltseq(vec) cat
						[ 0 : i in [4..dim] ]);
					return true, vec;
				end if;
			end for;
		end if;

		// If we're fine with a probabilitistic means of finding
		//  isotropic vectors, we can find them much faster.

		// Helpful definitions.
		a := subM[1,1]; b := subM[2,2]; c := subM[3,3];

		// We need to make sure we don't accidentally create the zero
		//  vector.
		repeat
			// Keep checking for isotropy until we find one.
			repeat
				// Pick a random non-zero vector.
				repeat v := Random(V);
				until v ne Zero(V);

				// Check if -(a*X^2 + b*Y^2)/c is a square.
				square, d :=
					IsSquare(-(a*v[1]^2 + b*v[2]^2) / c);
			until square;

			// Build the isotropic vector in the appropriate
			//  dimension, and return it.
			vec := v[1] * basis[1] + v[2] * basis[2] + d * basis[3];
			vec := Vector(Eltseq(vec) cat [ 0 : i in [4..dim] ]);
		until vec ne Zero(V);
		return true, vec;
	end if;

	// There are no isotropic vectors if we make it to this point!
	return false, _;
end function;

function SplitHyperbolicPlane(M, vec)
	// Get the relevant data structures.
	F, V, char, dim := VerifyMatrix(M);

	// The change of basis which preserving the isometry.
	basis := Id(GL(V));

	// Make a copy of the Gram matrix.
	gram := M;

	// Set the diagonal entries to zero when in characteristic 2.
	if char eq 2 then
		for i in [1..dim] do
			gram[i,i] := 0;
		end for;
	end if;

	// Save a copy of the original Gram matrix.
	originalGram := gram;

	// Find the pivot of the specified vector.
	pivot := 0;
	repeat pivot +:= 1;
	until vec[pivot] ne 0;

	// Perform the necessary basis changes so that vec becomes the first
	//  basis vector.
	MultiplyRow(~basis, vec[pivot], pivot);
	MultiplyColumn(~gram, vec[pivot], pivot);
	MultiplyRow(~gram, vec[pivot], pivot);
	for i in [pivot+1..dim] do
		AddRow(~basis, vec[i], i, pivot);
		AddColumn(~gram, vec[i], i, pivot);
		AddRow(~gram, vec[i], i, pivot);
	end for;
	SwapRows(~basis, 1, pivot);
	SwapColumns(~gram, 1, pivot);
	SwapRows(~gram, 1, pivot);

	// If the first row is entirely zero, then this vector belongs to the
	//  radical of the form.
	if gram[1] eq Zero(V) then
		if char eq 2 then
			// The quadratic form.
			Q := QF2(M);

			// Recover the quadratic form along the diagonal.
			for i in [1..dim] do
				gram[i,i] := Evaluate(Q, Eltseq(basis[i]));
			end for;
		end if;
		return gram, basis;
	end if;

	// Find a basis vector which is not orthogonal to our isotropic vector.
	idx := 1;
	repeat idx +:= 1;
	until gram[1,idx] ne 0;

	// Swap this basis vector with the second basis.
	SwapRows(~basis, 2, idx);
	SwapColumns(~gram, 2, idx);
	SwapRows(~gram, 2, idx);

	// Normalize the second basis vector so the (1,2)-entry is 1.
	scalar := 1/gram[1,2];
	MultiplyRow(~basis, scalar, 2);
	MultiplyColumn(~gram, scalar, 2);
	MultiplyRow(~gram, scalar, 2);

	// Determine the appropriate scalar for clearing out the (2,2)-entry.
	if char eq 2 then
		scalar := Evaluate(QF2(M), Eltseq(basis[2]));
	else
		scalar := -gram[2,2] / 2;
	end if;

	// Clear the (2,2)-entry in the Gram matrix.
	AddRow(~basis, scalar, 1, 2);
	AddColumn(~gram, scalar, 1, 2);
	AddRow(~gram, scalar, 1, 2);

	// Clear the remaining entries in the Gram matrix.
	for i in [3..dim] do
		// Clear first row/column.
		scalar := -gram[1,i];
		AddRow(~basis, scalar, 2, i);
		AddColumn(~gram, scalar, 2, i);
		AddRow(~gram, scalar, 2, i);

		// Clear second row/column.
		scalar := -gram[2,i];
		AddRow(~basis, scalar, 1, i);
		AddColumn(~gram, scalar, 1, i);
		AddRow(~gram, scalar, 1, i);
	end for;

	// Make sure we haven't made any mistakes.
	assert basis * originalGram * Transpose(basis) eq gram;

	// In characteristic 2, we need to recover the diagonal entries by
	//  evaluating the basis via the quadratic form.
	if char eq 2 then
		// The quadratic form.
		Q := QF2(M);
		for i in [1..dim] do
			gram[i,i] := Evaluate(Q, Eltseq(basis[i]));
		end for;
	end if;

	return gram, basis;
end function;

function HyperbolizeForm(M : Deterministic := true)
	// Verify that the supplied matrix has the proper credentials and save
	//  some of its properties for later use.
	F, V, char, dim := VerifyMatrix(M);

	// Find an isotropic vector if one exists.
	found, vec := FindIsotropicVector(M : Deterministic := Deterministic);

	// The space is anisotropic.
	if not found then
		// Change of basis matrix realizing the isometry.
		basis := Id(GL(V));

		// Make a copy of the Gram matrix.
		gram := M;

		if dim eq 1 then
			// Check if the (1,1)-entry is a square.
			sq, d := IsSquare(gram[1,1]);

			// If so, make it a 1.
			if sq then
				MultiplyRow(~basis, 1/d, 1);
				MultiplyColumn(~gram, 1/d, 1);
				MultiplyRow(~gram, 1/d, 1);
			end if;

			return gram, basis;
		elif char eq 2 then
			// Make the (1,1)-entry equal to 1.
			_, d := IsSquare(gram[1,1]);
			MultiplyRow(~basis, 1/d, 1);
			MultiplyColumn(~gram, 1/d, 1);
			MultiplyRow(~gram, 1/d, 1);

			// Make the (1,2)-entry equal to 1.
			scalar := 1/gram[1,2];
			MultiplyRow(~basis, scalar, 2);
			MultiplyColumn(~gram, scalar, 2);
			MultiplyRow(~gram, scalar, 2);

			return gram, basis;
		end if;

		// Clear the (1,2)-entry.
		scalar := -gram[1,2] / gram[1,1];
		AddRow(~basis, scalar, 1, 2);
		AddColumn(~gram, scalar, 1, 2);
		AddRow(~gram, scalar, 1, 2);

		// If the (2,2)-entry is a square, make it the first entry.
		sqB, d := IsSquare(gram[2,2]);
		if sqB then
			SwapRows(~basis, 1, 2);
			SwapColumns(~gram, 1, 2);
			SwapRows(~gram, 1, 2);
		end if;

		// Check if the (1,1)-entry is a square then clear it, if so.
		sqA, d := IsSquare(gram[1,1]);
		if sqA then
			MultiplyRow(~basis, 1/d, 1);
			MultiplyColumn(~gram, 1/d, 1);
			MultiplyRow(~gram, 1/d, 1);
		end if;

		// Check if M[2,2] is a square then clear it, if so..
		sqB, d := IsSquare(gram[2,2]);
		if sqB then
			MultiplyRow(~basis, 1/d, 2);
			MultiplyColumn(~gram, 1/d, 2);
			MultiplyRow(~gram, 1/d, 2);
		end if;

		// If neither are squares, make them -1 (note that this occurs
		//  if and only if -1 is not a square).
		if not sqA and not sqB then
			_, da := IsSquare(-gram[1,1]);
			_, db := IsSquare(-gram[2,2]);

			// Make the (1,1)-entry equal to -1.
			MultiplyRow(~basis, 1/da, 1);
			MultiplyColumn(~gram, 1/da, 1);
			MultiplyRow(~gram, 1/da, 1);

			// Make the (2,2)-entry equal to -1.
			MultiplyRow(~basis, 1/db, 2);
			MultiplyColumn(~gram, 1/db, 2);
			MultiplyRow(~gram, 1/db, 2);
		end if;

		return gram, basis;
	end if;

	// The quadratic form.
	Q := char eq 2 select QF2(M) else QuadraticForm(M);

	// Make sure the vector we found is isotropic.
	assert Evaluate(Q, Eltseq(vec)) eq 0;

	// Attempt to split a hyperbolic plane from the form.
	gram, basis := SplitHyperbolicPlane(M, vec);

	// Determine how many dimensions we need to split off.
	lowerDim := gram[1] eq Zero(V) select 1 else 2;

	if dim ge lowerDim + 1 then
		// Split the hyperbolic plane from the form.
		subM := Submatrix(gram, [lowerDim+1..dim], [lowerDim+1..dim]);

		// Iterate on the space orthogonal to the hyperbolic plane we
		//  just split off.
		subGram, subBasis :=
			HyperbolizeForm(subM : Deterministic := Deterministic);

		// Superimpose the lower-dimensional Gram matrix onto the
		//  original Gram matrix.
		gram := InsertBlock(gram, subGram, lowerDim+1, lowerDim+1);

		// Lift the subBasis to a higher-dimensional basis so that it
		//  preserves the previously computed bases.
		newBasis := Id(GL(V));
		newBasis :=
			InsertBlock(newBasis, subBasis, lowerDim+1, lowerDim+1);
		basis := newBasis * basis;
	end if;

	return gram, basis;
end function;

intrinsic Decompose(M::ModMatFldElt[FldFin]
		: BeCareful := true, Deterministic := false)
	-> AlgMatElt[FldFin], AlgMatElt[FldFin]
{ Decomposes the supplied quadratic form into a standard form and returns the
change-of-basis matrix which performs this transformation. }
	// Convert the matrix into a different form.
	M := Matrix(BaseRing(M), Nrows(M), Ncols(M), Eltseq(M));

	// Return the decomposition.
	return Decompose(M
		: BeCareful := BeCareful, Deterministic := Deterministic);
end intrinsic;

intrinsic Decompose(M::AlgMatElt[FldFin]
		: BeCareful := true, Deterministic := false)
	-> AlgMatElt[FldFin], AlgMatElt[FldFin]
{ Decomposes the supplied quadratic form into a standard form and returns the
change-of-basis matrix which performs this transformation. }
	// Verify that the matrix has proper credentials and save some of its
	//  properties for later.
	F, V, char, dim := VerifyMatrix(M);

	// Decompose the matrix into hyperbolic planes as much as possible.
	gram, basis := HyperbolizeForm(M : Deterministic := Deterministic);

	// Verify that everyhing we've done is correct.
	if char eq 2 then
		// The quadratic form.
		Q := QF2(M);

		// Verify that the basis evaluates correctly on the form.
		assert &and[ Evaluate(Q, Eltseq(basis[i])) eq gram[i,i]
			: i in [1..dim] ];

		// Zero out the diagonal to verify the bilinear form is correct.
		temp1 := gram; temp2 := M;
		for i in [1..dim] do
			temp1[i,i] := 0; temp2[i,i] := 0;
		end for;
	else
		temp1 := gram;
		temp2 := M;
	end if;

	// Verify that the bilinear forms are similar.
	assert basis * temp2 * Transpose(basis) eq temp1;

	// Let's bubble the basis vectors which belong to the radical to the
	//  end of the basis list.
	rad := 0;
	pos := dim;
	while pos ge 1 do
		if gram[pos] eq Zero(V) then
			rad +:= 1;
			for i in [pos+1..dim] do
				SwapRows(~basis, i-1, i);
				SwapColumns(~gram, i-1, i);
				SwapRows(~gram, i-1, i);
			end for;
		end if;
		pos -:= 1;
	end while;

	// Let's put the hyperbolic planes in our standard antidiagonal form.

	// The upper index of the hyperbolic space.
	upper := dim+1-rad;
	repeat upper -:= 1;
	until upper lt 1 or gram[upper,upper] eq 0;

	// Indices of the basis vectors we'll be swapping.
	i := 1;
	j := upper - 1;

	// Keep swapping basis vectors until j is less than or equal to i. Note
	//  that if there are no hyperbolic planes, this does nothing.
	while i lt j do
		SwapRows(~basis, i, j);
		SwapColumns(~gram, i, j);
		SwapRows(~gram, i, j);

		i +:= 2; j -:= 2;
	end while;

	// Since we did everything with row vectors, we need to transpose the
	//  basis, so that the subsequent code that utilizes it doesn't break.
	return gram, Transpose(basis);
end intrinsic;

