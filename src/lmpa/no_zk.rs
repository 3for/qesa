use crate::matrix::*;
use crate::transcript::TranscriptProtocol;
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use merlin::Transcript;
use std::io::Cursor;
use byteorder::{BigEndian};
use std::ops::{Add, Mul, Div};
use std::fmt::Debug;
use curve25519_dalek::traits::Identity;

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
pub struct lmpa_noZK{
    A_Matrix: Vec<Vec<RistrettoPoint>>,
    t_Vec: Vec<RistrettoPoint>,
    w_Vec: Vec<Scalar>,
    u_proof_Block: Vec<Vec<Vec<RistrettoPoint>>>,
}
pub fn create_lmpa_noZK(
    transcript: &mut Transcript,
    mut A: Vec<Vec<RistrettoPoint>>,
    mut w: Vec<Scalar>,
    mut t: Vec<RistrettoPoint>,
    mut n: usize, 
    m: usize,
    k: usize,
    one: Scalar,
    zero: RistrettoPoint,
) -> lmpa_noZK
{
    let mut u_proof: Vec<Vec<Vec<RistrettoPoint>>> = Vec::new();
    while n >= k {
        let chunk_size = n/k;
        let A_T = matrix_split(&A, chunk_size);
        let w_T: Vec<_> = matrix_split(&vec![w.clone()], chunk_size);
        println!("A_T:{:?}\n, w_T:{:?}", A_T, w_T);

        let mut i = 0;
        let mut j = 0;
        let shift = k-1; //to make the index begin with 0, index of -(k-1)
        let vec_len = 2*shift+1; // index 0~2*shift
        let mut u_vec: Vec<_> = vec![vec![zero; m]; vec_len];
        for A_t in A_T.clone() {
            for w_vec in w_T.clone() { 
                let l = shift + j - i;
                if( l != shift) {
                    let u_l_t = matrixpoint_vector_mul(&A_t, &w_vec[0]);
                    println!("u_l_t:{:?}, u_vec_l: {:?}", u_l_t, u_vec[l]);
                    u_vec[l] = rowpoint_rowpoint_add(&u_vec[l], &u_l_t);
                   
                } else {
                    u_vec[l] = t.clone(); 
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        i = 0;
        j = 0;

        println!("u_vec: {:?}", u_vec);

        for u_v in u_vec.iter() {
            for u_l in u_v.iter() {
                transcript.append_message(b"u_l", u_l.compress().as_bytes());
            }
        }
        u_proof.push(u_vec.clone());
        
        let x = transcript.challenge_scalar(b"challenge_x");

        let x_vec: Vec<_> = vandemonde_vector(x, k); 
        println!("x_vec: {:?}", x_vec);

        let y_vec: Vec<_> = vandemonde_vector(x.invert(), k); 
        println!("y_vec: {:?}, 1/x:{:?}", y_vec, x.invert());

        let mut z_vec: Vec<_> = vec![one; vec_len]; //default all as one.
        for x in x_vec.clone() {
            for y in y_vec.clone() {
                let l = shift + j - i;
                if( l != shift ) {
                    let z_l_t = &x * &y ;
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
            let tmp = matrixpoint_scalar_mul(&A_T[i], &x_vec[i]);
            if (new_A.len() == 0) {
                new_A.push(tmp);
            } else {
                new_A[0] = matrixpoint_matrix_add(&new_A[0], &tmp);
            }
            i += 1;
        }
        i = 0;
        
        A = new_A.pop().unwrap();
        println!("A: {:?}", A);

        let mut new_w: Vec<_> = Vec::new();
        while i < k {
            let tmp = matrix_scalar_mul(&w_T[i], &y_vec[i]);
            if (new_w.len() == 0) {
                new_w.push(tmp);
            } else {
                new_w[0] = matrix_matrix_add(&new_w[0], &tmp);
            }
            i += 1;
        }
        i = 0;

        w = new_w.pop().unwrap().pop().unwrap();
        println!("w:{:?}", w);

        let mut new_t: Vec<_> = Vec::new();
        while i < vec_len {
            let tmp = vectorpoint_scalar_mul(&u_vec[i], &z_vec[i]);
            if (new_t.len() == 0) {
                new_t.push(tmp);
            } else {
                new_t[0] = rowpoint_rowpoint_add(&new_t[0], &tmp);
            }
            i += 1;
        }
        println!("new_t:{:?}", new_t);
        t = new_t.pop().unwrap();
        println!("t:{:?}", t);

        i = 0;
        j = 0;
        n = n/k;
    }

    lmpa_noZK {
        A_Matrix: A,
        t_Vec: t,
        w_Vec: w,
        u_proof_Block: u_proof,
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

impl lmpa_noZK {
    pub fn verify_lmpa_noZK(
        &self,
        transcript: &mut Transcript,
        mut A: Vec<Vec<RistrettoPoint>>,
        mut t: Vec<RistrettoPoint>,
        mut n: usize, 
        m: usize,
        k: usize,
        one: Scalar,
        zero: RistrettoPoint,
    ) -> bool {
        let mut challenge_index = 0;
        while n >= k {
            let chunk_size = n/k;
            let A_T = matrix_split(&A, chunk_size);

            let mut i = 0;
            let mut j = 0;
            let shift = k-1; //to make the index begin with 0, index of -(k-1)
            let vec_len = 2*shift+1; // index 0~2*shift
            

            for u_v in self.u_proof_Block[challenge_index].iter() {
                for u_l in u_v.iter() {
                    transcript.append_message(b"u_l", u_l.compress().as_bytes());
                }
            }
            
            let x = transcript.challenge_scalar(b"challenge_x");

            let x_vec: Vec<_> = vandemonde_vector(x, k); 
            println!("x_vec: {:?}", x_vec);

            let y_vec: Vec<_> = vandemonde_vector(x.invert(), k); 
            println!("y_vec: {:?}, 1/x:{:?}", y_vec, x.invert());

            let mut z_vec: Vec<_> = vec![one; vec_len]; //default all as one.
            for x in x_vec.clone() {
                for y in y_vec.clone() {
                    let l = shift + j - i;
                    if( l != shift ) {
                        let z_l_t = &x * &y ;
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
                let tmp = matrixpoint_scalar_mul(&A_T[i], &x_vec[i]);
                if (new_A.len() == 0) {
                    new_A.push(tmp);
                } else {
                    new_A[0] = matrixpoint_matrix_add(&new_A[0], &tmp);
                }
                i += 1;
            }
            i = 0;
            
            A = new_A.pop().unwrap();
            println!("A: {:?}", A);

           

            let mut new_t: Vec<_> = Vec::new();
            while i < vec_len {
                let tmp = vectorpoint_scalar_mul(&self.u_proof_Block[challenge_index][i], &z_vec[i]);
                if (new_t.len() == 0) {
                    new_t.push(tmp);
                } else {
                    new_t[0] = rowpoint_rowpoint_add(&new_t[0], &tmp);
                }
                i += 1;
            }
            println!("new_t:{:?}", new_t);
            t = new_t.pop().unwrap();
            println!("t:{:?}", t);

            i = 0;
            j = 0;
            n = n/k;
            challenge_index += 1;
        }

        let expected_t = matrixpoint_vector_mul(&self.A_Matrix, &self.w_Vec);

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
fn test_lmpa_noZK_float() {
    /*let r_1 = vec![0,1,2,6,7,8];
    let r_2 = vec![3,4,5,9,10,11];
    let mut m: Vec<Vec<_>> = vec![r_1.clone()];
    m.push(r_2);
    println!("m: {:?}", m);
    let m_split = matrix_split(&m, 2);
    println!("m_split: {:?}", m_split);*/
    
    // Realise protocol 3.9 in qesa with float values for easy test.

    let k: usize = 4; 
    let d: u32 = 3;
    let mut n = k.pow(d);
    println!("n:{}", n);
    let m = 1;
    let mut i = 0;
    let mut A: Vec<_> = Vec::new();
    while i < m {
        let my_vec: Vec<f64> = (i*n..(i+1)*n).map(|i| i as f64).collect();
        A.push(my_vec);
        i += 1;
    }

    let mut w: Vec<f64> = (0..n).map(|i| i as f64).collect();

    println!("A:{:?}\n, w:{:?}", A, w);
    let origin_t = matrix_vector_mul_general(&A, &w, 0.0 );
    println!("############# origin_t A*w:{:?}", origin_t);

    let mut t: Vec<_> = origin_t;

    while n >= k {
        let chunk_size = n/k;
        let A_T = matrix_split(&A, chunk_size);
        let w_T: Vec<_> = matrix_split(&vec![w.clone()], chunk_size);
        println!("A_T:{:?}\n, w_T:{:?}", A_T, w_T);

        let mut i = 0;
        let mut j = 0;
        let shift = k-1; //to make the index begin with 0, index of -(k-1)
        let vec_len = 2*shift+1; // index 0~2*shift
        let mut u_vec: Vec<_> = vec![vec![0.0; m]; vec_len];
        for A_t in A_T.clone() {
            for w_vec in w_T.clone() { 
                let l = shift + j - i;
                if( l != shift) {
                    let u_l_t: Vec<f64> = matrix_vector_mul_general(&A_t, &w_vec[0], 0.0 );
                    println!("j:{:?}, i:{:?}, l:{:?}, u_l_t:{:?}", j, i, l, u_l_t);
                    u_vec[l] = row_row_add_general(&u_vec[l], &u_l_t);
                   
                } else {
                    u_vec[l] = t.clone(); 
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        i = 0;
        j = 0;

        println!("u_vec: {:?}", u_vec);

        let x: f64= 2.0; //rand::random::<f64>(); //random float calc may have rounding error.
        /*let mut transcript = Transcript::new(b"protocol 3.9 float test");
        let mut buf = [0u8; 32];
        transcript.challenge_bytes(b"challenge_x", &mut buf);
        let mut rdr = Cursor::new(buf);
        let x: f64 = rdr.read_f64::<BigEndian>().unwrap();*/

        
        let x_vec: Vec<_> = vandemonde_vector_general(x, k, 1 as f64); 
        println!("x_vec: {:?}", x_vec);

        let y_vec: Vec<_> = vandemonde_vector_general(1.0/(x as f64), k, 1.0); 
        println!("y_vec: {:?}, 1/x:{:?}", y_vec, 1.0/(x as f64) );

        let mut z_vec: Vec<_> = vec![1.0; vec_len]; //default all as one.
        for x in x_vec.clone() {
            for y in y_vec.clone() {
                let l = shift + j - i;
                if( l != shift ) {
                    let z_l_t = (x as f64) * (y as f64);
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

        w = new_w.pop().unwrap().pop().unwrap();
        println!("w:{:?}", w);

        let mut new_t: Vec<_> = Vec::new();
        while i < vec_len {
            let tmp = vector_scalar_mul_general(&u_vec[i], &z_vec[i]);
            if (new_t.len() == 0) {
                new_t.push(tmp);
            } else {
                new_t[0] = row_row_add_general(&new_t[0], &tmp);
            }
            i += 1;
        }
        println!("new_t:{:?}", new_t);
        t = new_t.pop().unwrap();
        println!("t:{:?}", t);

        i = 0;
        j = 0;
        n = n/k;
    }

    let verifier_t = matrix_vector_mul_general(&A, &w, 0.0 );
    println!("new############# A*w:{:?}", verifier_t);
    assert_eq!(verifier_t, t);
}

#[test]
fn test_lmpa_noZK_merlin() {
    // using merlin to make the protocol 3.9 non-interactive.

    let k: usize = 5; 
    let d: u32 = 3;
    let mut n = k.pow(d);
    println!("n:{}", n);
    let m = 4;
    let mut rng = rand::thread_rng();
    let A = rand_matrix(m, n);
    let w: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
    let mut t = matrixpoint_vector_mul(&A, &w);

    let mut transcript = Transcript::new(b"protocol 3.9 float test");
    let proof = create_lmpa_noZK(
        &mut transcript,
        A.clone(),
        w,
        t.clone(),
        n, //cols
        m, //rows
        k, //k
        Scalar::one(), //one
        RistrettoPoint::identity(), //zero
    );

    let mut verifier_transcript = Transcript::new(b"protocol 3.9 float test");
    assert!(proof.verify_lmpa_noZK(&mut verifier_transcript, A, t, n, m, k, Scalar::one(), RistrettoPoint::identity()));
}

#[test]
fn test_lmpa_almSnd_float() {    
    // Realise protocol 3.14 in qesa with float values for easy test.
    let k: usize = 2; 
    let d: u32 = 1;
    let mut n = k.pow(d);
    println!("n:{}", n);
    let m = 2;
    let mut i = 0;
    let mut A: Vec<_> = Vec::new();
    while i < m {
        let my_vec: Vec<f64> = (i*n..(i+1)*n).map(|i| i as f64).collect();
        A.push(my_vec);
        i += 1;
    }
    let mut w: Vec<_> = (0..n).map(|i| i as f64).collect();

    let mut H: Vec<Vec<Vec<_>>> = Vec::new();
    let mut t_all: Vec<Vec<_>> = Vec::new();
    println!("A:{:?}\n, w:{:?}", A, w);
    let mut origin_t = matrix_vector_mul_general(&A, &w, 0.0 );
    println!("############# origin_t A*w:{:?}", origin_t);
    t_all.push(origin_t.clone());
    let mut r: Vec<Vec<_>> = Vec::new();
    r.push(vec![0.0; n]);
    H.push(A.clone());
    i = 0;
    while i < m {
        let mut tmp: Vec<Vec<_>> = vec![vec![0.0; n]; m];
        let my_vec: Vec<f64> = (i*n..(i+1)*n).map(|i| i as f64).collect();
        tmp[i] = my_vec;
        let mut r_i: Vec<f64> = (0..n).map(|j| (j+i) as f64).collect();
        let t_i = matrix_vector_mul_general(&tmp, &r_i, 0.0 );
        r.push(r_i);
        H.push(tmp);
        t_all.push(t_i);
        i += 1;
    }
    i = 0;

    let mut x_challenge_vec: Vec<f64> = (0..m+1).map(|j| (j+2) as f64).collect();

    println!("H:{:?}, t_all: {:?}, x_challenge_vec:{:?}", H, t_all, x_challenge_vec);
    println!("r:{:?}", r);


    let mut w_all: Vec<Vec<_>> = vec![vec![0.0;n];m+1];
    w_all[0] = vector_scalar_mul_general(&w.clone(), &x_challenge_vec[0]);
    for i in 1..m+1 {
        w_all[i] = vector_scalar_mul_general(&r[i], &x_challenge_vec[i]);
    }
    println!("w_all:{:?}", w_all);



  

    let mut t: Vec<_> = origin_t;
    let mut m_index = 0;
    for h in H.iter() {
        A = h.clone();
        w = w_all[m_index].clone();
    while n >= k {
        let chunk_size = n/k;
        let A_T = matrix_split(&A, chunk_size);
        let w_T: Vec<_> = matrix_split(&vec![w.clone()], chunk_size);
        println!("A_T:{:?}\n, w_T:{:?}", A_T, w_T);

        let mut i = 0;
        let mut j = 0;
        let shift = k-1; //to make the index begin with 0, index of -(k-1)
        let vec_len = 2*shift+1; // index 0~2*shift
        let mut u_vec: Vec<_> = vec![vec![0.0; m]; vec_len];
        for A_t in A_T.clone() {
            for w_vec in w_T.clone() { 
                let l = shift + j - i;
                if( l != shift) {
                    let u_l_t: Vec<f64> = matrix_vector_mul_general(&A_t, &w_vec[0], 0.0 );
                    println!("j:{:?}, i:{:?}, l:{:?}, u_l_t:{:?}", j, i, l, u_l_t);
                    u_vec[l] = row_row_add_general(&u_vec[l], &u_l_t);
                   
                } else {
                    u_vec[l] = t.clone(); 
                }
                j += 1;
            }
            i += 1;
            j = 0;
        }
        i = 0;
        j = 0;

        println!("u_vec: {:?}", u_vec);

        let x: f64= 2.0; //rand::random::<f64>(); //random float calc may have rounding error.
        /*let mut transcript = Transcript::new(b"protocol 3.9 float test");
        let mut buf = [0u8; 32];
        transcript.challenge_bytes(b"challenge_x", &mut buf);
        let mut rdr = Cursor::new(buf);
        let x: f64 = rdr.read_f64::<BigEndian>().unwrap();*/

        
        let x_vec: Vec<_> = vandemonde_vector_general(x, k, 1 as f64); 
        println!("x_vec: {:?}", x_vec);

        let y_vec: Vec<_> = vandemonde_vector_general(1.0/(x as f64), k, 1.0); 
        println!("y_vec: {:?}, 1/x:{:?}", y_vec, 1.0/(x as f64) );

        let mut z_vec: Vec<_> = vec![1.0; vec_len]; //default all as one.
        for x in x_vec.clone() {
            for y in y_vec.clone() {
                let l = shift + j - i;
                if( l != shift ) {
                    let z_l_t = (x as f64) * (y as f64);
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

        w = new_w.pop().unwrap().pop().unwrap();
        println!("w:{:?}", w);

        let mut new_t: Vec<_> = Vec::new();
        while i < vec_len {
            let tmp = vector_scalar_mul_general(&u_vec[i], &z_vec[i]);
            if (new_t.len() == 0) {
                new_t.push(tmp);
            } else {
                new_t[0] = row_row_add_general(&new_t[0], &tmp);
            }
            i += 1;
        }
        println!("new_t:{:?}", new_t);
        t = new_t.pop().unwrap();
        println!("t:{:?}", t);

        i = 0;
        j = 0;
        n = n/k;
    }
    //m_index += 1;
    }

    let verifier_t = matrix_vector_mul_general(&A, &w, 0.0 );
    println!("new############# A*w:{:?}", verifier_t);
    assert_eq!(verifier_t, t);
}