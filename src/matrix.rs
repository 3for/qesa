#![allow(non_snake_case)]
use crate::math_utils::inner_product;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use std::ops::{Add, Mul};
use std::fmt::Debug;

// Multiplies every element in the matrix by the scalar
// Returns the new matrix
pub fn matrix_scalar_mul(matrix: &Vec<Vec<Scalar>>, x: &Scalar) -> Vec<Vec<Scalar>> {
    matrix
        .iter()
        .map(|row| row.iter().map(|elem| elem * x).collect())
        .collect()
}
// Takes a matrix and a vector
// Returns a new vector i.e. (Ax=b)
pub fn matrix_vector_mul(matrix: &Vec<Vec<Scalar>>, vec: &[Scalar]) -> Vec<Scalar> {
    matrix.iter().map(|row| inner_product(row, &vec)).collect()
}

// Takes two rows and adds them together
// The (i) entry of row a is added to the i entry of row b
pub fn row_row_add(row_a: &[Scalar], row_b: &[Scalar]) -> Vec<Scalar> {
    assert_eq!(row_a.len(), row_b.len());

    row_a.iter().zip(row_b.iter()).map(|(a, b)| a + b).collect()
}

// Takes two rows and subtracts them
// The (i) entry of row a is subtracted from the i entry of row b
pub fn row_row_sub(row_a: &[Scalar], row_b: &[Scalar]) -> Vec<Scalar> {
    assert_eq!(row_a.len(), row_b.len());

    row_a.iter().zip(row_b.iter()).map(|(a, b)| a - b).collect()
}

// Takes two matrices and adds them together
// The (i,j) entry of matrix A is added to the (i,j) entry of B
pub fn matrix_matrix_add(A: &Vec<Vec<Scalar>>, B: &Vec<Vec<Scalar>>) -> Vec<Vec<Scalar>> {
    assert_eq!(A.len(), B.len());

    A.iter()
        .zip(B.iter())
        .map(|(row_a, row_b)| row_row_add(row_a, row_b))
        .collect()
}

// Takes the transpose of a matrix
pub fn matrix_transpose(matrix: &Vec<Vec<Scalar>>) -> Vec<Vec<Scalar>> {
    let mut transpose: Vec<Vec<Scalar>> = vec![Vec::new(); matrix[0].len()];

    for (_, row) in matrix.iter().enumerate() {
        for (i, element) in row.iter().enumerate() {
            transpose[i].push(element.clone());
        }
    }

    transpose
}

pub struct BlockMatrix {
    pub block: Vec<Vec<Vec<Scalar>>>,
}

impl BlockMatrix {
    pub fn new() -> BlockMatrix {
        BlockMatrix { block: Vec::new() }
    }
    pub fn push(&mut self, matrix: Vec<Vec<Scalar>>) {
        self.block.push(matrix)
    }
    pub fn with(matrix: Vec<Vec<Scalar>>) -> BlockMatrix {
        let mut b = BlockMatrix { block: Vec::new() };

        b.block.push(matrix);
        b
    }
    // Takes a block matrix and uses challenges to batch all vectors together into one matrix
    // by summing them
    pub fn block_matrix_batch(&self, challenges: &[Scalar]) -> Vec<Vec<Scalar>> {
        // This returns the block of matrices with each matrix multiplied by challenge
        let block_challenge: Vec<Vec<Vec<Scalar>>> = self
            .block
            .iter()
            .zip(challenges.iter())
            .map(|(matrix, challenge)| matrix_scalar_mul(matrix, challenge))
            .collect();

        // sums up each matrix
        let mut sum_block = block_challenge[0].clone();
        for i in 1..block_challenge.len() {
            sum_block = matrix_matrix_add(&sum_block, &block_challenge[i])
        }

        sum_block
    }
}

// Point

// Multiplies every element in the matrix by the scalar
// Returns the new matrix
pub fn matrixpoint_scalar_mul(
    matrix: &Vec<Vec<RistrettoPoint>>,
    x: &Scalar,
) -> Vec<Vec<RistrettoPoint>> {
    matrix
        .iter()
        .map(|row| row.iter().map(|elem| elem * x).collect())
        .collect()
}
// Takes a matrix and a vector
// Returns a new vector i.e. (Ax=b)
pub fn matrixpoint_vector_mul(
    matrix: &Vec<Vec<RistrettoPoint>>,
    vec: &[Scalar],
) -> Vec<RistrettoPoint> {
    matrix
        .iter()
        .map(|row| {
            let vals: Vec<RistrettoPoint> =
                row.iter().zip(vec.iter()).map(|(a, b)| a * b).collect();

            let mut ip = RistrettoPoint::identity();
            for val in vals {
                ip = ip + val;
            }

            ip
        })
        .collect()
}

// More general! 
// Takes a matrix and a vector
// Returns a new vector i.e. (Ax=b)
pub fn matrix_vector_mul_general<T>(
    matrix: &Vec<Vec<T>>,
    vec: &[T],
    identity: T, //zero val.
) -> Vec<T> 
where 
    T: Mul<Output=T> + Add<Output=T> + Copy + Clone, 
{
    matrix
        .iter()
        .map(|row| {
            let vals: Vec<T> =
                row.iter().zip(vec.iter()).map(|(a, b)| *a * *b).collect();

            let mut ip = identity;
            for val in vals {
                ip = ip + val;
            }

            ip
        })
        .collect()
}

// More general!
// Multiplies every element in the matrix by the scalar
// Returns the new matrix
pub fn matrix_scalar_mul_general<T>(
    matrix: &Vec<Vec<T>>,
    x: &T,
) -> Vec<Vec<T>> 
where 
    T: Mul<Output=T> + Add<Output=T> + Copy + Clone + Debug, 
{
    matrix
        .iter()
        .map(|row| row.iter().map(|elem| *elem * *x).collect())
        .collect()
}

// More general!
// Multiplies every element in the vector by the scalar
// Returns the new vector
pub fn vector_scalar_mul_general<T>(
    in_vec: &Vec<T>,
    x: &T,
) -> Vec<T> 
where 
    T: Mul<Output=T> + Add<Output=T> + Copy + Clone + Debug, 
{
    in_vec
        .iter()
        .map(|elem| *elem * *x)
        .collect()
}

// Multiplies every element in the vector by the scalar
// Returns the new vector
pub fn vectorpoint_scalar_mul(
    in_vec: &Vec<RistrettoPoint>,
    x: &Scalar,
) -> Vec<RistrettoPoint> 
{
    in_vec
        .iter()
        .map(|elem| elem * x)
        .collect()
}

// More general!
// Takes two rows and adds them together
// The (i) entry of row a is added to the i entry of row b
pub fn row_row_add_general<T>(
    row_a: &[T],
    row_b: &[T],
) -> Vec<T> 
where T: Add<Output=T> + Copy + Clone {
    assert_eq!(row_a.len(), row_b.len());

    row_a.iter().zip(row_b.iter()).map(|(a, b)| *a + *b).collect()
}

// More general!
// Takes two matrices and adds them together
// The (i,j) entry of matrix A is added to the (i,j) entry of B
pub fn matrix_matrix_add_general<T>(A: &Vec<Vec<T>>, B: &Vec<Vec<T>>) -> Vec<Vec<T>> 
where 
    T: Add<Output=T> + Copy + Clone,
{
    assert_eq!(A.len(), B.len());

    A.iter()
        .zip(B.iter())
        .map(|(row_a, row_b)| row_row_add_general(row_a, row_b))
        .collect()
}

// Takes two rows and adds them together
// The (i) entry of row a is added to the i entry of row b
pub fn rowpoint_rowpoint_add(
    row_a: &[RistrettoPoint],
    row_b: &[RistrettoPoint],
) -> Vec<RistrettoPoint> {
    assert_eq!(row_a.len(), row_b.len());

    row_a.iter().zip(row_b.iter()).map(|(a, b)| a + b).collect()
}
// Takes two matrices and adds them together
// The (i,j) entry of matrix A is added to the (i,j) entry of B
pub fn matrixpoint_matrix_add(
    A: &Vec<Vec<RistrettoPoint>>,
    B: &Vec<Vec<RistrettoPoint>>,
) -> Vec<Vec<RistrettoPoint>> {
    assert_eq!(A.len(), B.len());

    A.iter()
        .zip(B.iter())
        .map(|(row_a, row_b)| rowpoint_rowpoint_add(row_a, row_b))
        .collect()
}


pub fn matrixpoint_transpose(
    matrix: &Vec<Vec<RistrettoPoint>>,
) -> Vec<Vec<RistrettoPoint>> {
    let m = matrix.len();
    assert!(m > 0);
    let n = matrix[0].len();
    println!("zouyudi-m:{:?}, n:{:?}", m, n);
    let mut matrix_transpose = vec![Vec::new(); matrix[0].len()];
    /*matrix
        .iter().enumerate()
        .map(|(i, row)| {
            let vals: Vec<RistrettoPoint> =
                row.iter().enumerate().map(|(j, b)| {matrix_transpose[j][i] = *b; matrix_transpose[j][i]}).collect();
            vals
        })
        .collect()*/

    for (_, row) in matrix.iter().enumerate() {
        for (i, element) in row.iter().enumerate() {
            matrix_transpose[i].push(element.clone());
        }
    }
    matrix_transpose
}

pub fn matrix_split<T: Copy>(
    matrix: &Vec<Vec<T>>,
    chunk_size: usize, 
) -> Vec<Vec<Vec<T>>> {
    let m = matrix.len();
    assert!(m > 0);
    let n = matrix[0].len();
    assert!(n%chunk_size == 0);

    let mut matrix_splited: Vec<_>= vec![Vec::new(); n/chunk_size];
    for (_, row) in matrix.iter().enumerate() {
        let mut r_chunks: Vec<_> = row.chunks(chunk_size).collect();
        let mut i = 0;
        for r_chunk in r_chunks {
            matrix_splited[i].push(r_chunk.to_vec());
            i += 1;
        }
    }
   
    matrix_splited
}



pub fn vandemonde_matrix(m: usize, n: usize) -> Vec<Vec<Scalar>> {
    let mut rng = rand::thread_rng();

    let mut matrix: Vec<Vec<Scalar>> = Vec::new();

    for _ in 0..m {
        let challenge: Scalar = Scalar::random(&mut rng);
        let a: Vec<Scalar> = vandemonde_vector(challenge, n);

        matrix.push(a);
    }

    matrix
}

pub fn vandemonde_vector(mut x: Scalar, n: usize) -> Vec<Scalar> {
    let mut challenges: Vec<Scalar> = Vec::new();
    challenges.push(Scalar::one());
    for i in 0..n-1 {
        challenges.push(challenges[i] * x);
    }

    challenges
}

pub fn vandemonde_vector_general<T>(mut x: T, n: usize, one: T) -> Vec<T> 
where 
    T: Mul<Output=T> + Add<Output=T> + Copy + Clone,
{
    let mut challenges: Vec<T> = Vec::new();
    challenges.push(one);
    for i in 0..n-1 {
        challenges.push(challenges[i] * x);
    }

    challenges
}

pub fn rand_matrix(m: usize, n: usize) -> Vec<Vec<RistrettoPoint>> {
    let mut rng = rand::thread_rng();

    let mut matrix: Vec<Vec<RistrettoPoint>> = Vec::new();

    for _ in 0..m {
        let a: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();

        matrix.push(a);
    }

    matrix
}
