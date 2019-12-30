use crate::lmpa::no_zk;
use crate::matrix::*;
use crate::transcript::TranscriptProtocol;
use curve25519_dalek::{
    ristretto::RistrettoPoint, 
    scalar::Scalar,
    traits::VartimeMultiscalarMul,
    traits::Identity
    };
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
    //In qesa paper section 3.4.3, computing [A]r for random r is expensive.
    let a = matrixpoint_vector_mul(&A, &r); 
    for element in a.iter() {
        transcript.append_message(b"a", element.compress().as_bytes());
    }

    let beta = transcript.challenge_scalar(b"beta");
    //Blinding the witness.
    let w_prime = w
        .iter()
        .zip(r.iter())
        .map(|(witness, random)| beta * witness + random)
        .collect();

    let proof = no_zk::create(transcript, A, G_Vec, H_Vec, &Q, w_prime);

    SimpleZK { a: a, no_zk: proof }
}

// Linear Map Pre-Image Argument without zero knowledge
// Protocol 3.13 in qesa paper.
pub struct SimpleZK_general {
    lamp_no_zk: no_zk::lmpa_noZK,
    a: Vec<RistrettoPoint>,
}

pub fn create_general(
    transcript: &mut Transcript,
    mut A: Vec<Vec<RistrettoPoint>>,
    mut w: Vec<Scalar>,
    mut t: Vec<RistrettoPoint>,
    mut n: usize, 
    m: usize,
    k: usize,
) -> SimpleZK_general {

    let mut rng = rand::thread_rng();
    let r: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    //In qesa paper section 3.4.3, computing [A]r for random r is expensive.
    let a = matrixpoint_vector_mul(&A, &r); 
    for element in a.iter() {
        transcript.append_message(b"a", element.compress().as_bytes());
    }

    let beta = transcript.challenge_scalar(b"beta");
    //Blinding the witness.
    let w_prime: Vec<Scalar> = w
        .iter()
        .zip(r.iter())
        .map(|(witness, random)| beta * witness + random)
        .collect();

    let proof = no_zk::create_lmpa_noZK(
        transcript,
        A.clone(),
        w,
        t.clone(),
        n, //cols
        m, //rows
        k, //k
        Scalar::one(), //one
        RistrettoPoint::identity(), //zero
    );

    SimpleZK_general { a: a, lamp_no_zk: proof }
}

impl SimpleZK_general {
    pub fn verify_general(
        &self,
        transcript: &mut Transcript,
        mut A: Vec<Vec<RistrettoPoint>>,
        mut t: Vec<RistrettoPoint>,
        mut n: usize, 
        m: usize,
        k: usize,
    ) -> bool {

        for element in self.a.iter() {
            transcript.append_message(b"a", element.compress().as_bytes());
        }
        let beta = transcript.challenge_scalar(b"beta");

        t = t
            .iter()
            .zip(self.a.iter())
            .map(|(t_i, a_i)| beta * t_i + a_i)
            .collect();

        self.lamp_no_zk.verify_lmpa_noZK(transcript, A, t, n, m, k, Scalar::one(), RistrettoPoint::identity())
    }
}

impl SimpleZK {
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        mut A: Vec<Vec<RistrettoPoint>>,
        G_Vec: Vec<RistrettoPoint>,
        H_Vec: Vec<RistrettoPoint>,
        Q: &RistrettoPoint,
        n: usize,
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
fn test_lmpa_ZK_merlin() {
    let k: usize = 5; 
    let d: u32 = 3;
    let mut n = k.pow(d);
    let m = 4;
    let mut rng = rand::thread_rng();
    let A = rand_matrix(m, n);
    let w: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let mut t = matrixpoint_vector_mul(&A, &w);

    let mut transcript = Transcript::new(b"protocol 3.13 test");
    let proof = create_general(
        &mut transcript,
        A.clone(),
        w,
        t.clone(),
        n, //cols
        m, //rows
        k, //k
    );

    let mut verifier_transcript = Transcript::new(b"protocol 3.13 test");
    assert!(proof.verify_general(&mut verifier_transcript, A, t, n, m, k));
}



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
    let n = 2;
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

#[test]
fn test_commitment_combination() {
    let n = 1;
    let mut rng = rand::thread_rng();

    let G: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let G0: RistrettoPoint = RistrettoPoint::random(&mut rng);

    let w_1 = Scalar::random(&mut rng);
    let w_2 = Scalar::random(&mut rng);
    let r_1 = Scalar::random(&mut rng);
    let r_2 = Scalar::random(&mut rng);
    let c_1 = pedersen_commit(&G0, &G.clone(), &vec![w_1.clone()], &r_1);
    let c_2 = pedersen_commit(&G0, &G.clone(), &vec![w_2.clone()], &r_2);
    let a_1 = &Scalar::random(&mut rng);
    let a_2 = &Scalar::random(&mut rng);
    let w_combined = &w_1 * a_1 + &w_2 * a_2;
    let r_combined = &r_1 * a_1 + &r_2 * a_2;
    let c_combined = pedersen_commit(&G0, &G.clone(), &vec![w_combined.clone()], &r_combined);
    assert_eq!(a_1 * &c_1 + a_2*&c_2, c_combined);
}

#[test]
fn test_lmpa_batch() {
    // Step 3.3 in qesa paper.
    // Efficient communication based on 1.1.1 Probabilistic Verification in qesa paper.
    // where vector y is [y,y^2,...,y^m], and a is a single point independent of m.
    let n = 7;
    let m = 4;
    let mut rng = rand::thread_rng();

    let G: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let H: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");
    let Y: Vec<Scalar> = vandemonde_vector(Scalar::random(&mut rng), m); 
    let G0: RistrettoPoint = RistrettoPoint::random(&mut rng);

    // t = Aw
    let A = rand_matrix(m, n);
    let A_T = matrixpoint_transpose(&A);
    let A_T_Y = matrixpoint_vector_mul(&A_T, &Y);
    let A_efficient = vec![A_T_Y.clone(); 1];
    let w: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    
    // pedersen commitment of w.
    let r_w: Scalar = Scalar::random(&mut rng);
    let c_w = pedersen_commit(&G0, &G.clone(), &w.clone(), &r_w);
 
    let t = matrixpoint_vector_mul(&A_efficient.clone(), &w);
    let t_efficient = matrixpoint_vector_mul(&matrixpoint_transpose(&vec![t; 1]), &Y);

    //    
    let mut B: Vec<Vec<RistrettoPoint>> = Vec::new();
    let mut tmp: Vec<RistrettoPoint> = vec![G0];
    tmp.extend_from_slice(&G);
    B.push(tmp);
    tmp = vec![RistrettoPoint::identity()];
    tmp.extend_from_slice(&A_T_Y);
    B.push(tmp);
    let mut r_w_w: Vec<Scalar> = vec![r_w];
    r_w_w.extend_from_slice(&w);

    //let c_w_1 = matrixpoint_vector_mul(&vec![B[0].clone()], &r_w_w);
    //println!("zouyudi c_w: {:?}, c_w_1: {:?}", c_w, c_w_1);
    //assert_eq!(c_w[0].compress(), c_w_1.compress());
    let mut u: Vec<RistrettoPoint> = vec![c_w];
    u.extend_from_slice(&t_efficient);

    let new_n = n+1; // Attention to this var.
    let new_G = B[0].clone(); //TODO: actually G_vec and H_vec is unneccessary in create() and verify().

    let mut prover_transcript = Transcript::new(b"lmpa_simple_zk");
    let proof = create(
        &mut prover_transcript,
        B.clone(),
        new_G.clone(),
        H.clone(),
        &Q,
        r_w_w,
    );

    let mut verifier_transcript = Transcript::new(b"lmpa_simple_zk");
    assert!(proof.verify(&mut verifier_transcript, B, new_G, H, &Q, new_n, u));
}

pub fn pedersen_commit(
    H: &RistrettoPoint,
    G_Vec: &[RistrettoPoint],
    msg: &[Scalar],
    rand: &Scalar,
) -> RistrettoPoint {

    let mut commitment = RistrettoPoint::vartime_multiscalar_mul(msg.iter(), G_Vec.iter());

    // Add random scalar
    commitment = commitment + H * rand;

    commitment
}

