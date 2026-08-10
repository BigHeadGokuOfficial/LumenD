use axum::{
    extract::Json,
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::{get, post},
    Router,
};
use base64::{engine::general_purpose::STANDARD, Engine};
use luau_lifter::decompile_bytecode;
use serde::{Deserialize, Serialize};
use std::panic::{catch_unwind, AssertUnwindSafe};
use tokio::{net::TcpListener, task};

#[derive(Deserialize)]
struct Req {
    bytecode: String,
    key: Option<u8>,
}

#[derive(Serialize)]
struct Res {
    success: bool,
    source: Option<String>,
    backend: &'static str,
    error: Option<String>,
}

fn json(code: StatusCode, data: Res) -> Response {
    (code, Json(data)).into_response()
}

async fn health() -> Response {
    Json(serde_json::json!({
        "success": true,
        "backend": "medal"
    }))
    .into_response()
}

async fn decomp(Json(req): Json<Req>) -> Response {
    let raw = match STANDARD.decode(req.bytecode.as_bytes()) {
        Ok(v) => v,
        Err(e) => {
            return json(
                StatusCode::BAD_REQUEST,
                Res {
                    success: false,
                    source: None,
                    backend: "medal",
                    error: Some(e.to_string()),
                },
            )
        }
    };

    let key = req.key.unwrap_or(203);

    let job = task::spawn_blocking(move || {
        catch_unwind(AssertUnwindSafe(|| decompile_bytecode(&raw, key)))
    })
    .await;

    match job {
        Ok(Ok(src)) if !src.trim().is_empty() => json(
            StatusCode::OK,
            Res {
                success: true,
                source: Some(src),
                backend: "medal",
                error: None,
            },
        ),
        Ok(Ok(_)) => json(
            StatusCode::UNPROCESSABLE_ENTITY,
            Res {
                success: false,
                source: None,
                backend: "medal",
                error: Some("empty source".to_string()),
            },
        ),
        Ok(Err(_)) => json(
            StatusCode::UNPROCESSABLE_ENTITY,
            Res {
                success: false,
                source: None,
                backend: "medal",
                error: Some("decompiler panic".to_string()),
            },
        ),
        Err(e) => json(
            StatusCode::INTERNAL_SERVER_ERROR,
            Res {
                success: false,
                source: None,
                backend: "medal",
                error: Some(e.to_string()),
            },
        ),
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/health", get(health))
        .route("/decompile", post(decomp));

    let net = TcpListener::bind("127.0.0.1:7331").await.unwrap();

    println!("lumend-native 127.0.0.1:7331");

    axum::serve(net, app).await.unwrap();
}
