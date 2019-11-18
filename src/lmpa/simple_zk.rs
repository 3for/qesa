use crate::lmpa::no_zk;
use crate::matrix::*;
use crate::transcript::TranscriptProtocol;
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use merlin::Transcript;

// Linear Map Pre-Image Argument without zero knowledge
pub struct SimpleZK {
    no_zk: no_zk::NoZK,
    a: Vec<RistrettoPoint>,
}

pub fn create(
    transcript: &mut Transcript,
    mut A: Vec<Vec<RistrettoPoint>>,
    G_Vec: Vec<RistrettoPoint>,
    H_Vec: Vec<RistrettoPoint>,
    Q: &RistrettoPoint,
    w: Vec<Scalar>,
) -> SimpleZK {
    let mut n = G_Vec.len();

    let mut rng = rand::thread_rng();
    let r: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();

    let a = matrixpoint_vector_mul(&A, &r);
    for element in a.iter() {
        transcript.append_message(b"a", element.compress().as_bytes());
    }

    let beta = transcript.challenge_scalar(b"beta");

    let w_prime = w
        .iter()
        .zip(r.iter())
        .map(|(witness, random)| beta * witness + random)
        .collect();

    let proof = no_zk::create(transcript, A, G_Vec, H_Vec, &Q, w_prime);

    SimpleZK { a: a, no_zk: proof }
}


impl SimpleZK {
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        mut A: Vec<Vec<RistrettoPoint>>,
        G_Vec: Vec<RistrettoPoint>,
        H_Vec: Vec<RistrettoPoint>,
        Q: &RistrettoPoint,
        mut n: usize,
        mut t: Vec<RistrettoPoint>,
    ) -> bool {
        assert_eq!(n, G_Vec.len());

        for element in self.a.iter() {
            transcript.append_message(b"a", element.compress().as_bytes());
        }
        let beta = transcript.challenge_scalar(b"beta");

        t = t
            .iter()
            .zip(self.a.iter())
            .map(|(t_i, a_i)| beta * t_i + a_i)
            .collect();

        self.no_zk.verify(transcript, A, G_Vec, H_Vec, &Q, n, t)
    }
}

use sha3::Sha3_512;

#[test]
fn test_lmpa_simple_zk_create_verify() {
    let n = 4;
    let m = 4;
    let mut rng = rand::thread_rng();

    let G: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let H: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");

    let mut prover_transcript = Transcript::new(b"lmpa_simple_zk");

    // t = Aw
    let A = rand_matrix(m, n);
    let w: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let t = matrixpoint_vector_mul(&A, &w);

    let proof = create(
        &mut prover_transcript,
        A.clone(),
        G.clone(),
        H.clone(),
        &Q,
        w,
    );

    let mut verifier_transcript = Transcript::new(b"lmpa_simple_zk");
    assert!(proof.verify(&mut verifier_transcript, A.clone(), G.clone(), H.clone(), &Q, n, t.clone()));
    let mut verifier_transcript2 = Transcript::new(b"lmpa_simple_zk");
    assert!(proof.verify(&mut verifier_transcript2, A, G, H, &Q, n, t));
}
#[test]
fn test_lmpa_simple_zk_create_verify_efficient_communication() {
    // Efficient communication based on 1.1.1 Probabilistic Verification in qesa paper.
    // where vector y is [y,y^2,...,y^m], and a is a single point independent of m.
    let n = 4;
    let m = 4;
    let mut rng = rand::thread_rng();

    let G: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let H: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");
    let Y: Vec<Scalar> = vandemonde_vector(Scalar::random(&mut rng), m); 


    let mut prover_transcript = Transcript::new(b"lmpa_simple_zk");

    // t = Aw
    let A = rand_matrix(m, n);
    let A_T = matrixpoint_transpose(&A);
    let A_efficient = vec![matrixpoint_vector_mul(&A_T, &Y); 1];
    let w: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let t = matrixpoint_vector_mul(&A_efficient.clone(), &w);
    let t_efficient = matrixpoint_vector_mul(&matrixpoint_transpose(&vec![t; 1]), &Y);

    let proof = create(
        &mut prover_transcript,
        A_efficient.clone(),
        G.clone(),
        H.clone(),
        &Q,
        w,
    );

    let mut verifier_transcript = Transcript::new(b"lmpa_simple_zk");
    assert!(proof.verify(&mut verifier_transcript, A_efficient, G, H, &Q, n, t_efficient));
}

fn rand_matrix(m: usize, n: usize) -> Vec<Vec<RistrettoPoint>> {
    let mut rng = rand::thread_rng();

    let mut matrix: Vec<Vec<RistrettoPoint>> = Vec::new();

    for _ in 0..m {
        let a: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();

        matrix.push(a);
    }

    matrix
}

fn vandemonde_matrix(m: usize, n: usize) -> Vec<Vec<Scalar>> {
    let mut rng = rand::thread_rng();

    let mut matrix: Vec<Vec<Scalar>> = Vec::new();

    for _ in 0..m {
        let challenge: Scalar = Scalar::random(&mut rng);
        let a: Vec<Scalar> = vandemonde_vector(challenge, n);

        matrix.push(a);
    }

    matrix
}

fn vandemonde_vector(mut x: Scalar, n: usize) -> Vec<Scalar> {
    let mut challenges: Vec<Scalar> = Vec::new();
    challenges.push(Scalar::one());
    for _ in 1..n {
        challenges.push(x);
        x = x * x;
    }

    challenges
}