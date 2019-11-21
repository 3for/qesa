use crate::matrix::*;
use crate::transcript::TranscriptProtocol;
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use merlin::Transcript;
// Linear Map Pre-Image Argument without zero knowledge
pub struct NoZK {
    L_Vec: Vec<Vec<RistrettoPoint>>,
    R_Vec: Vec<Vec<RistrettoPoint>>,
    w: Scalar,
}
pub fn create(
    transcript: &mut Transcript,
    mut A: Vec<Vec<RistrettoPoint>>,
    G_Vec: Vec<RistrettoPoint>,
    H_Vec: Vec<RistrettoPoint>,
    Q: &RistrettoPoint,
    mut w: Vec<Scalar>,
) -> NoZK {
    let mut n = G_Vec.len();

    let mut L_Vec: Vec<Vec<RistrettoPoint>> = Vec::new();
    let mut R_Vec: Vec<Vec<RistrettoPoint>> = Vec::new();

    while n != 1 {
        n = n / 2;
        let (A_0_1): Vec<_> = A
            .iter()
            .map(|row| {
                let (left, right) = row.split_at(row.len() / 2);

                (left.to_owned(), right.to_owned())
            })
            .collect();

        let (A_0): Vec<_> = A_0_1.iter().map(|(vec_left, _)| vec_left.clone()).collect();
        let (A_1): Vec<_> = A_0_1
            .iter()
            .map(|(_, vec_right)| vec_right.clone())
            .collect();

        let (w_0, w_1) = w.split_at(w.len() / 2);

        let L = matrixpoint_vector_mul(&A_0, w_1);
        for u_L in L.iter() {
            transcript.append_message(b"L", u_L.compress().as_bytes());
        }
        L_Vec.push(L);

        let R = matrixpoint_vector_mul(&A_1, w_0);
        for u_R in R.iter() {
            transcript.append_message(b"R", u_R.compress().as_bytes());
        }
        R_Vec.push(R);

        let challenge = transcript.challenge_scalar(b"challenge");
        println!("zouyudi-create challenge:{:?}", challenge);

        let challenge_matrix = matrixpoint_scalar_mul(&A_1, &challenge);
        A = matrixpoint_matrix_add(&A_0, &challenge_matrix);

        w = w_0
            .iter()
            .zip(w_1.iter())
            .map(|(a, b)| a * challenge + b)
            .collect();
    }

    NoZK {
        L_Vec: L_Vec,
        R_Vec: R_Vec,
        w: w[0],
    }
}

// For protocol 3.9 in qesa paper.
pub struct lmpa_noZK {
    A_Matrix: Vec<Vec<RistrettoPoint>>,
    t_Vec: Vec<RistrettoPoint>,
    w_Vec: Vec<Scalar>,
    n: usize,
}
pub fn create_lmpa_noZK(
    transcript: &mut Transcript,
    mut A: Vec<Vec<RistrettoPoint>>,
    G_Vec: Vec<RistrettoPoint>,
    H_Vec: Vec<RistrettoPoint>,
    Q: &RistrettoPoint,
    mut w: Vec<Scalar>,
    mut n: usize, 
    k: usize,
) -> lmpa_noZK {
    let mut m = A[0].len();
    assert_eq!(m, n);

    let mut L_Vec: Vec<Vec<RistrettoPoint>> = Vec::new();
    let mut R_Vec: Vec<Vec<RistrettoPoint>> = Vec::new();
    

    while n > k {
        let A_m = matrix_split(&A, k);
        n = n / k;
        let (A_0_1): Vec<_> = A
            .iter()
            .map(|row| {
                let (left, right) = row.split_at(row.len() / 2);

                (left.to_owned(), right.to_owned())
            })
            .collect();

        let (A_0): Vec<_> = A_0_1.iter().map(|(vec_left, _)| vec_left.clone()).collect();
        let (A_1): Vec<_> = A_0_1
            .iter()
            .map(|(_, vec_right)| vec_right.clone())
            .collect();

        let (w_0, w_1) = w.split_at(w.len() / 2);

        let L = matrixpoint_vector_mul(&A_0, w_1);
        for u_L in L.iter() {
            transcript.append_message(b"L", u_L.compress().as_bytes());
        }
        L_Vec.push(L);

        let R = matrixpoint_vector_mul(&A_1, w_0);
        for u_R in R.iter() {
            transcript.append_message(b"R", u_R.compress().as_bytes());
        }
        R_Vec.push(R);

        let challenge = transcript.challenge_scalar(b"challenge");
        println!("zouyudi-create challenge:{:?}", challenge);

        let challenge_matrix = matrixpoint_scalar_mul(&A_1, &challenge);
        A = matrixpoint_matrix_add(&A_0, &challenge_matrix);

        w = w_0
            .iter()
            .zip(w_1.iter())
            .map(|(a, b)| a * challenge + b)
            .collect();
    }

    lmpa_noZK {
        A_Matrix: A,
        t_Vec: R_Vec[0].clone(),
        w_Vec: w,
        n: n,
    }
}

impl NoZK {
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

        let mut challenge_index = 0;

        while n != 1 {
            n = n / 2;

            let (A_0_1): Vec<_> = A
                .iter()
                .map(|row| {
                    let (left, right) = row.split_at(row.len() / 2);

                    (left.to_owned(), right.to_owned())
                })
                .collect();

            let (A_0): Vec<_> = A_0_1.iter().map(|(vec_left, _)| vec_left.clone()).collect();
            let (A_1): Vec<_> = A_0_1
                .iter()
                .map(|(_, vec_right)| vec_right.clone())
                .collect();

            // Add challenges to transcript
            for u_L in self.L_Vec[challenge_index].iter() {
                transcript.append_message(b"L", u_L.compress().as_bytes());
            }
            for u_R in self.R_Vec[challenge_index].iter() {
                transcript.append_message(b"R", u_R.compress().as_bytes());
            }

            let challenge = transcript.challenge_scalar(b"challenge");
            println!("zouyudi-verify challenge:{:?}", challenge);
            let challenge_matrix = matrixpoint_scalar_mul(&A_1, &challenge);
            A = matrixpoint_matrix_add(&A_0, &challenge_matrix);

            t = self.L_Vec[challenge_index]
                .iter()
                .zip(self.R_Vec[challenge_index].iter())
                .zip(t.iter())
                .map(|((l, r), t)| l + (challenge * t) + (challenge * challenge * r))
                .collect();

            challenge_index += 1;
        }

        let base_witnes = vec![self.w];

        let expected_t = matrixpoint_vector_mul(&A, &base_witnes);

        expected_t[0] == t[0]
    }
}
use sha3::Sha3_512;

#[test]
fn test_lmpa_no_zk_create_verify() {
    let n = 4;
    let m = 4;
    let mut rng = rand::thread_rng();

    let G: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let H: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");

    let mut prover_transcript = Transcript::new(b"lmpa_no_zk");

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

    let mut verifier_transcript = Transcript::new(b"lmpa_no_zk");
    assert!(proof.verify(&mut verifier_transcript, A, G, H, &Q, n, t));
}

#[test]
fn test_matrix_split() {
    /*let r_1 = vec![0,1,2,6,7,8];
    let r_2 = vec![3,4,5,9,10,11];
    let mut m: Vec<Vec<_>> = vec![r_1.clone()];
    m.push(r_2);
    println!("m: {:?}", m);
    let m_split = matrix_split(&m, 2);
    println!("m_split: {:?}", m_split);*/

    let k: usize = 2; 
    let d: u32 = 3;
    let mut n = k.pow(d);
    println!("n:{}", n);
    let m = 4;
    let mut i = 0;
    let mut A: Vec<_> = Vec::new();
    while i < m {
        let my_vec: Vec<f64> = (i*n..(i+1)*n).map(|i| i as f64).collect();
        A.push(my_vec);
        i += 1;
    }

    let mut w: Vec<f64> = (0..n).map(|i| i as f64).collect();
    //let mut w = (0..n).collect::<Vec<_>>();

    println!("A:{:?}\n, w:{:?}", A, w);
    println!("############# A*w:{:?}", matrix_vector_mul_general(&A, &w, 0.0 ));

    while n > k {
        let chunk_size = n/k;
        let A_T = matrix_split(&A, chunk_size);
        let w_T: Vec<_> = matrix_split(&vec![w.clone()], chunk_size);
        //let w_vec = w_T.pop().unwrap();
        println!("A_T:{:?}\n, w_T:{:?}", A_T, w_T);

        let mut i = 0;
        let mut j = 0;
        let mut u_vec: Vec<_> = vec![vec![0.0; m]; 2*k+1];
        for A_t in A_T.clone() {
            for w_vec in w_T.clone() {
                println!("w_vec:{:?}", w_vec);
                println!("A_t:{:?}, j:{:?}, i:{:?}, k:{:?}", A_t, j, i, k);
                let l = k + j - i;
                if( l != k) {
                    let u_l_t: Vec<f64> = matrix_vector_mul_general(&A_t, &w_vec[0], 0.0 );
                    println!("l:{:?}, u_l_t:{:?}", l, u_l_t);
                    u_vec[l] = row_row_add_general(&u_vec[l], &u_l_t);
                   
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        i = 0;
        j = 0;

        println!("u_vec: {:?}", u_vec);

        let x: f64= 2.0;
        let x_vec: Vec<_> = vandemonde_vector_general(x, k, 1 as f64); 
        println!("x_vec: {:?}", x_vec);

        let y_vec: Vec<_> = vandemonde_vector_general(1.0/(x as f64), k, 1.0); 
        println!("y_vec: {:?}, 1/x:{:?}", y_vec, 1.0/(x as f64) );

        let mut z_vec: Vec<_> = vec![1.0; 2*k+1];
        for x in x_vec.clone() {
            for y in y_vec.clone() {
                println!("x:{:?}, j:{:?}, i:{:?}, k:{:?}", x, j, i, k);
                let l = k + j - i;
                if( l != k) {
                    let z_l_t = (x as f64) * (y as f64);
                    println!("l:{:?}, z_l_t:{:?}", l, z_l_t);
                    z_vec[l] = z_l_t;
                   
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        i = 0;
        j = 0;
        println!("z_vec: {:?}", z_vec);

        let mut new_A: Vec<_> = Vec::new();
        while i < k {
            let tmp = matrix_scalar_mul_general(&A_T[i], &x_vec[i]);
            if (new_A.len() == 0) {
                new_A.push(tmp);
            } else {
                new_A[0] = matrix_matrix_add_general(&new_A[0], &tmp);
            }
            i += 1;
        }
        i = 0;
        
        A = new_A.pop().unwrap();
        println!("A: {:?}", A);

        let mut new_w: Vec<_> = Vec::new();
        while i < k {
            let tmp = matrix_scalar_mul_general(&w_T[i], &y_vec[i]);
            if (new_w.len() == 0) {
                new_w.push(tmp);
            } else {
                new_w[0] = matrix_matrix_add_general(&new_w[0], &tmp);
            }
            i += 1;
        }
        i = 0;

        println!("new_w:{:?}", new_w);
        w = new_w.pop().unwrap().pop().unwrap();
        println!("w:{:?}", w);

        i = 0;
        j = 0;
        n = n/k;
    }

    println!("new############# A*w:{:?}", matrix_vector_mul_general(&A, &w, 0.0 ));
}

#[test]
fn test_lmpa_noZK() {
    // See section 3.4.2 in qesa paper. Procotol 3.9.
    let k: usize = 2; 
    let d: u32 = 3;
    let mut n = k.pow(d);
    println!("zouyudi n:{}", n);
    let m = 4;
    let mut rng = rand::thread_rng();

    let G: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let H: Vec<RistrettoPoint> = (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");

    let mut prover_transcript = Transcript::new(b"lmpa_no_zk");

    // t = Aw
    let A = rand_matrix(m, n);
    let w: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let t = matrixpoint_vector_mul(&A, &w);

     while n > k {
        let chunk_size = n/k;
        let A_T = matrix_split(&A, chunk_size);
        let mut w_T = matrix_split(&vec![w.clone()], chunk_size);
        let w_vec = w_T.pop().unwrap();

        let mut i = 0;
        let mut j = 0;
        //let mut u_vec = Vec::new();
        for A_t in A_T {
           /*w_vec.iter().enumerate()
            .map(|(j, w_t)|
                let l = j - i;
                if( l != 0) {
                    let u_l_t = matrixpoint_vector_mul(&A_t, &w_t.to_vec())
                    if(u_vec.len() > l) {
                        u_vec[l].push(rowpoint_rowpoint_add(&u_vec[l], u_l_t));
                    } else {
                        u_vec[l].push(u_l_t);
                    }
                }
            );*/
            i += 1;
        }

        n = n/k;
     }

    let proof = create(
        &mut prover_transcript,
        A.clone(),
        G.clone(),
        H.clone(),
        &Q,
        w,
    );

    let mut verifier_transcript = Transcript::new(b"lmpa_no_zk");
    assert!(proof.verify(&mut verifier_transcript, A, G, H, &Q, n, t));
}